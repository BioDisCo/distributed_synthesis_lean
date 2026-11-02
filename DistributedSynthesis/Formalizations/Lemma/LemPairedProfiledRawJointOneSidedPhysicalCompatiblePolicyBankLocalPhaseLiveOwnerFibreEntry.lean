/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatiblePolicyBankLocalPhaseLiveOwnerFibreKernel
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionPostResolveRecurrentPolicyBank

/-!
# Entry from a post-resolve bank root into the owner-fibre kernel

The post-resolve construction produces an admissible bank root carrying the
physical table selected at the same semantic target.  This file turns either
installed oriented move in that table into the matched-prefix boundary
certificate required by the recurrent owner-fibre kernel.
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

/-- A right move stored at an admissible bank root initializes a genuine
right matched-prefix boundary at the empty local prefix. -/
theorem profiledRawJointRecurrentRightBoundaryInvariant_bankRoot
    (key : RootKey A strategy)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (hmove : key.1.2.1 = some move)
    (root : ProfiledRawJointThreadRoot A)
    (hroot :
      profiledRawJointOneSidedCurrentSlots A .right key.1.1 () = some root)
    (row : PairedEntryRow)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A) :
    ProfiledRawJointRecurrentRightBoundaryInvariant A strategy hwin
      (profiledRawJointOneSidedPhysicalCompatibleBankRoot A strategy hwin key,
        ⟨initialProfiledRawJointRightPhysicalSiblingReceiver A move row,
          (move.memberController A false).initial⟩,
        oldReceiver) := by
  refine ⟨key.1.1, root, [],
    profiledRawJointOneSidedPhysicalCompatibleBankRoot_reachable A strategy
      hwin key, ?_, hroot, ?_, ?_, ?_⟩
  · exact congrArg Prod.fst
      (profiledRawJointOneSidedPhysicalCompatibleBankRoot_data A strategy hwin
        key)
  · have hdata := congrArg (fun data ↦ data.2.1)
      (profiledRawJointOneSidedPhysicalCompatibleBankRoot_data A strategy hwin
        key)
    exact hdata.trans hmove
  · rfl
  · rfl

/-- Mirrored initialization from a left move stored at an admissible bank
root. -/
theorem profiledRawJointRecurrentLeftBoundaryInvariant_bankRoot
    (key : RootKey A strategy)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hmove : key.1.2.2 = some move)
    (root : ProfiledRawJointThreadRoot A)
    (hroot :
      profiledRawJointOneSidedCurrentSlots A .left key.1.1 () = some root)
    (row : PairedEntryRow)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A) :
    ProfiledRawJointRecurrentLeftBoundaryInvariant A strategy hwin
      (profiledRawJointOneSidedPhysicalCompatibleBankRoot A strategy hwin key,
        ⟨initialProfiledRawJointLeftPhysicalSiblingReceiver A move row,
          (move.memberController A false).initial⟩,
        oldReceiver) := by
  refine ⟨key.1.1, root, [],
    profiledRawJointOneSidedPhysicalCompatibleBankRoot_reachable A strategy
      hwin key, ?_, hroot, ?_, ?_, ?_⟩
  · exact congrArg Prod.fst
      (profiledRawJointOneSidedPhysicalCompatibleBankRoot_data A strategy hwin
        key)
  · have hdata := congrArg (fun data ↦ data.2.2)
      (profiledRawJointOneSidedPhysicalCompatibleBankRoot_data A strategy hwin
        key)
    exact hdata.trans hmove
  · rfl
  · rfl

/-! ## Actual post-resolve target entries -/

/-- Every row target reached at an arbitrary depth of the process-one
post-resolve block supplies a left-oriented matched-prefix boundary at the
corresponding recurrent bank root.  The bank index and the installed move
come from the same occurrence-linked target payload. -/
theorem
    profiledRawJointStrictLeftPostResolveLinkedMovePlay_leftBoundary_exists
    (initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy)
    (entry input : In₁ × In₂)
    (member : Bool) (env : Nat → In₂ × In₁) (n : Nat)
    (row : PairedEntryRow)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A) :
    let play := profiledRawJointStrictLeftPostResolveLinkedMovePlay A strategy
      hwin initial entry input member env
    let projected := BlockRecordMonitor.projectReceiverPlay
      (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A)
      play
    let delivered :=
      (((projected n).2.1.target row).1,
        (profiledRawJointHybridFinitePayloadLinkedTargetPayload A
          ((projected n).2.1.target row)) member)
    ∃ (key : RootKey A strategy)
        (move : ProfiledRawJointLeftPhysicalSiblingMove A),
      key.1 = delivered ∧
        ProfiledRawJointRecurrentLeftBoundaryInvariant A strategy hwin
          (profiledRawJointOneSidedPhysicalCompatibleBankRoot A strategy hwin
              key,
            ⟨initialProfiledRawJointLeftPhysicalSiblingReceiver A move row,
              (move.memberController A false).initial⟩,
            oldReceiver) := by
  dsimp only
  let play := profiledRawJointStrictLeftPostResolveLinkedMovePlay A strategy
    hwin initial entry input member env
  let projected := BlockRecordMonitor.projectReceiverPlay
    (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A)
    play
  obtain ⟨past, nextInput, htarget⟩ :=
    profiledRawJointStrictLeftPostResolveLinkedMovePlay_target_exists A
      strategy hwin initial entry input member env n row
  have htarget' :
      (projected n).2.1.target row =
        ((profiledRawJointStrictLeftPostResolveLinkedActivation A strategy
            hwin initial entry input member).target row past nextInput,
          (row,
            profiledRawJointStrictLeftPostResolveLinkedChildren A strategy
              hwin initial entry input
              (.strict (profiledRawJointUnitRightActualDirection row past
                nextInput)))) := by
    simpa only [projected, play] using htarget
  let key :=
    profiledRawJointStrictLeftPostResolveRecurrentTargetKey A strategy hwin
      initial entry input member row past nextInput
  let delivered :=
    (((projected n).2.1.target row).1,
      (profiledRawJointHybridFinitePayloadLinkedTargetPayload A
        ((projected n).2.1.target row)) member)
  have hkey : key.1 = delivered := by
    have hkeyBase :
        key.1 =
          ((profiledRawJointStrictLeftPostResolveLinkedActivation A strategy
              hwin initial entry input member).target row past nextInput,
            profiledRawJointStrictLeftPostResolveLinkedChildren A strategy
              hwin initial entry input
              (.strict (profiledRawJointUnitRightActualDirection row past
                nextInput)) member) := by
      simpa [key] using
        (profiledRawJointStrictLeftPostResolveRecurrentTargetKey_data A
          strategy hwin initial entry input member row past nextInput)
    calc
      key.1 = _ := hkeyBase
      _ = delivered := by
        dsimp only [delivered]
        rw [htarget']
        simp only [profiledRawJointHybridFinitePayloadLinkedTargetPayload]
  obtain ⟨move, hmove, hroot⟩ :=
    profiledRawJointStrictLeftPostResolveLinkedChildren_move_exists A strategy
      hwin initial entry input member row past nextInput
  have hkeyMove : key.1.2.2 = some move := by
    calc
      key.1.2.2 = delivered.2.2 :=
        congrArg (fun data ↦ data.2.2) hkey
      _ = (profiledRawJointStrictLeftPostResolveLinkedChildren A strategy hwin
          initial entry input
          (.strict (profiledRawJointUnitRightActualDirection row past
            nextInput)) member).2 := by
        dsimp only [delivered]
        rw [htarget']
        simp only [profiledRawJointHybridFinitePayloadLinkedTargetPayload]
      _ = some move := hmove
  have hkeyRoot :
      profiledRawJointOneSidedCurrentSlots A .left key.1.1 () =
        some (.inr move.1.source) := by
    calc
      profiledRawJointOneSidedCurrentSlots A .left key.1.1 () =
          profiledRawJointOneSidedCurrentSlots A .left delivered.1 () := by
        rw [congrArg Prod.fst hkey]
      _ = profiledRawJointOneSidedCurrentSlots A .left
          ((profiledRawJointStrictLeftPostResolveLinkedActivation A strategy
            hwin initial entry input member).target row past nextInput) () := by
        dsimp only [delivered]
        rw [htarget']
      _ = some (.inr move.1.source) := hroot
  refine ⟨key, move, hkey, ?_⟩
  exact
    profiledRawJointRecurrentLeftBoundaryInvariant_bankRoot A strategy hwin key
      move hkeyMove (.inr move.1.source) hkeyRoot row oldReceiver

/-- Process-two mirror: every arbitrary-depth post-resolve target supplies a
right-oriented matched-prefix boundary at its occurrence-linked bank root. -/
theorem
    profiledRawJointStrictRightPostResolveLinkedMovePlay_rightBoundary_exists
    (initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy)
    (entry input : In₁ × In₂)
    (member : Bool) (env : Nat → In₁ × In₂) (n : Nat)
    (row : PairedEntryRow)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A) :
    let play := profiledRawJointStrictRightPostResolveLinkedMovePlay A strategy
      hwin initial entry input member env
    let projected := BlockRecordMonitor.projectReceiverPlay
      (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A)
      play
    let delivered :=
      (((projected n).2.1.target row).1,
        (profiledRawJointHybridFinitePayloadLinkedTargetPayload A
          ((projected n).2.1.target row)) member)
    ∃ (key : RootKey A strategy)
        (move : ProfiledRawJointRightPhysicalSiblingMove A),
      key.1 = delivered ∧
        ProfiledRawJointRecurrentRightBoundaryInvariant A strategy hwin
          (profiledRawJointOneSidedPhysicalCompatibleBankRoot A strategy hwin
              key,
            ⟨initialProfiledRawJointRightPhysicalSiblingReceiver A move row,
              (move.memberController A false).initial⟩,
            oldReceiver) := by
  dsimp only
  let play := profiledRawJointStrictRightPostResolveLinkedMovePlay A strategy
    hwin initial entry input member env
  let projected := BlockRecordMonitor.projectReceiverPlay
    (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A)
    play
  obtain ⟨past, nextInput, htarget⟩ :=
    profiledRawJointStrictRightPostResolveLinkedMovePlay_target_exists A
      strategy hwin initial entry input member env n row
  have htarget' :
      (projected n).2.1.target row =
        ((profiledRawJointStrictRightPostResolveLinkedActivation A strategy
            hwin initial entry input member).target row past nextInput,
          (row,
            profiledRawJointStrictRightPostResolveLinkedChildren A strategy
              hwin initial entry input
              (.strict (profiledRawJointUnitLeftActualDirection row past
                nextInput)))) := by
    simpa only [projected, play] using htarget
  let key :=
    profiledRawJointStrictRightPostResolveRecurrentTargetKey A strategy hwin
      initial entry input member row past nextInput
  let delivered :=
    (((projected n).2.1.target row).1,
      (profiledRawJointHybridFinitePayloadLinkedTargetPayload A
        ((projected n).2.1.target row)) member)
  have hkey : key.1 = delivered := by
    have hkeyBase :
        key.1 =
          ((profiledRawJointStrictRightPostResolveLinkedActivation A strategy
              hwin initial entry input member).target row past nextInput,
            profiledRawJointStrictRightPostResolveLinkedChildren A strategy
              hwin initial entry input
              (.strict (profiledRawJointUnitLeftActualDirection row past
                nextInput)) member) := by
      simpa [key] using
        (profiledRawJointStrictRightPostResolveRecurrentTargetKey_data A
          strategy hwin initial entry input member row past nextInput)
    calc
      key.1 = _ := hkeyBase
      _ = delivered := by
        dsimp only [delivered]
        rw [htarget']
        simp only [profiledRawJointHybridFinitePayloadLinkedTargetPayload]
  obtain ⟨move, hmove, hroot⟩ :=
    profiledRawJointStrictRightPostResolveLinkedChildren_move_exists A strategy
      hwin initial entry input member row past nextInput
  have hkeyMove : key.1.2.1 = some move := by
    calc
      key.1.2.1 = delivered.2.1 :=
        congrArg (fun data ↦ data.2.1) hkey
      _ = (profiledRawJointStrictRightPostResolveLinkedChildren A strategy hwin
          initial entry input
          (.strict (profiledRawJointUnitLeftActualDirection row past
            nextInput)) member).1 := by
        dsimp only [delivered]
        rw [htarget']
        simp only [profiledRawJointHybridFinitePayloadLinkedTargetPayload]
      _ = some move := hmove
  have hkeyRoot :
      profiledRawJointOneSidedCurrentSlots A .right key.1.1 () =
        some (.inl move.1.source) := by
    calc
      profiledRawJointOneSidedCurrentSlots A .right key.1.1 () =
          profiledRawJointOneSidedCurrentSlots A .right delivered.1 () := by
        rw [congrArg Prod.fst hkey]
      _ = profiledRawJointOneSidedCurrentSlots A .right
          ((profiledRawJointStrictRightPostResolveLinkedActivation A strategy
            hwin initial entry input member).target row past nextInput) () := by
        dsimp only [delivered]
        rw [htarget']
      _ = some (.inl move.1.source) := hroot
  refine ⟨key, move, hkey, ?_⟩
  exact
    profiledRawJointRecurrentRightBoundaryInvariant_bankRoot A strategy hwin
      key move hkeyMove (.inl move.1.source) hkeyRoot row oldReceiver

/-! ## Finite readback at actual post-resolve targets -/

/-- At every process-one post-resolve target, finite readback of the delivered
public payload succeeds.  The returned key is the same key that carries the
left-oriented matched-prefix boundary; no realizability decision is supplied
to the handoff. -/
theorem
    profiledRawJointStrictLeftPostResolveLinkedMovePlay_leftBoundary_readback_exists
    (initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy)
    (entry input : In₁ × In₂)
    (member : Bool) (env : Nat → In₂ × In₁) (n : Nat)
    (row : PairedEntryRow)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A) :
    let play := profiledRawJointStrictLeftPostResolveLinkedMovePlay A strategy
      hwin initial entry input member env
    let projected := BlockRecordMonitor.projectReceiverPlay
      (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A)
      play
    let delivered :=
      (((projected n).2.1.target row).1,
        (profiledRawJointHybridFinitePayloadLinkedTargetPayload A
          ((projected n).2.1.target row)) member)
    ∃ (key : RootKey A strategy)
        (move : ProfiledRawJointLeftPhysicalSiblingMove A),
      profiledRawJointOneSidedPhysicalCompatibleRootKey? A strategy
          delivered = some key ∧
        ProfiledRawJointRecurrentLeftBoundaryInvariant A strategy hwin
          (profiledRawJointOneSidedPhysicalCompatibleBankRoot A strategy hwin
              key,
            ⟨initialProfiledRawJointLeftPhysicalSiblingReceiver A move row,
              (move.memberController A false).initial⟩,
            oldReceiver) := by
  dsimp only
  obtain ⟨key, move, hkey, hinvariant⟩ :=
    profiledRawJointStrictLeftPostResolveLinkedMovePlay_leftBoundary_exists A
      strategy hwin initial entry input member env n row oldReceiver
  obtain ⟨found, hread, hfound⟩ :=
    profiledRawJointOneSidedPhysicalCompatibleRootKey?_complete A strategy
      _ key hkey
  subst found
  exact ⟨key, move, hread, hinvariant⟩

/-- Process-two mirror of finite readback at an arbitrary-depth post-resolve
target. -/
theorem
    profiledRawJointStrictRightPostResolveLinkedMovePlay_rightBoundary_readback_exists
    (initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy)
    (entry input : In₁ × In₂)
    (member : Bool) (env : Nat → In₁ × In₂) (n : Nat)
    (row : PairedEntryRow)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A) :
    let play := profiledRawJointStrictRightPostResolveLinkedMovePlay A strategy
      hwin initial entry input member env
    let projected := BlockRecordMonitor.projectReceiverPlay
      (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A)
      play
    let delivered :=
      (((projected n).2.1.target row).1,
        (profiledRawJointHybridFinitePayloadLinkedTargetPayload A
          ((projected n).2.1.target row)) member)
    ∃ (key : RootKey A strategy)
        (move : ProfiledRawJointRightPhysicalSiblingMove A),
      profiledRawJointOneSidedPhysicalCompatibleRootKey? A strategy
          delivered = some key ∧
        ProfiledRawJointRecurrentRightBoundaryInvariant A strategy hwin
          (profiledRawJointOneSidedPhysicalCompatibleBankRoot A strategy hwin
              key,
            ⟨initialProfiledRawJointRightPhysicalSiblingReceiver A move row,
              (move.memberController A false).initial⟩,
            oldReceiver) := by
  dsimp only
  obtain ⟨key, move, hkey, hinvariant⟩ :=
    profiledRawJointStrictRightPostResolveLinkedMovePlay_rightBoundary_exists A
      strategy hwin initial entry input member env n row oldReceiver
  obtain ⟨found, hread, hfound⟩ :=
    profiledRawJointOneSidedPhysicalCompatibleRootKey?_complete A strategy
      _ key hkey
  subst found
  exact ⟨key, move, hread, hinvariant⟩

/-! ## Direct entry into the operational recurrent carrier -/

/-- A process-one post-resolve target, followed by any first recurrent input,
enters the concrete owner-fibre carrier in its left-oriented operational
relation.  The bank root used in the carrier is exactly the result of finite
readback of the delivered post-resolve payload. -/
theorem
    profiledRawJointStrictLeftPostResolveLinkedMovePlay_operational_exists
    (initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy)
    (entry input recurrentInput : In₁ × In₂)
    (member : Bool) (env : Nat → In₂ × In₁) (n : Nat)
    (row : PairedEntryRow)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A) :
    let play := profiledRawJointStrictLeftPostResolveLinkedMovePlay A strategy
      hwin initial entry input member env
    let projected := BlockRecordMonitor.projectReceiverPlay
      (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A)
      play
    let delivered :=
      (((projected n).2.1.target row).1,
        (profiledRawJointHybridFinitePayloadLinkedTargetPayload A
          ((projected n).2.1.target row)) member)
    ∃ (key : RootKey A strategy)
        (move : ProfiledRawJointLeftPhysicalSiblingMove A),
      profiledRawJointOneSidedPhysicalCompatibleRootKey? A strategy
          delivered = some key ∧
        let data :
            ProfiledRawJointRecurrentLeftBoundaryData A strategy hwin :=
          (profiledRawJointOneSidedPhysicalCompatibleBankRoot A strategy hwin
              key,
            ⟨initialProfiledRawJointLeftPhysicalSiblingReceiver A move row,
              (move.memberController A false).initial⟩,
            rightTemplate)
        let packet :=
          profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A
            strategy hwin data.1 (data.target A strategy hwin recurrentInput)
        ∃ rightMove : ProfiledRawJointRightPhysicalSiblingMove A,
          packet.successor.2.1.2.1 = some rightMove ∧
            ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy
              hwin
              (profiledRawJointRecurrentOwnerFibreLeftEntryOne A strategy hwin
                data.1 (data.receiver A strategy hwin) packet)
              (profiledRawJointRecurrentOwnerFibreLeftEntryTwo A strategy hwin
                data.1 (data.receiver A strategy hwin)
                  (data.owner A strategy hwin) rightTemplate packet) := by
  dsimp only
  obtain ⟨key, move, hread, hinvariant⟩ :=
    profiledRawJointStrictLeftPostResolveLinkedMovePlay_leftBoundary_readback_exists
      A strategy hwin initial entry input member env n row rightTemplate
  let data : ProfiledRawJointRecurrentLeftBoundaryData A strategy hwin :=
    (profiledRawJointOneSidedPhysicalCompatibleBankRoot A strategy hwin key,
      ⟨initialProfiledRawJointLeftPhysicalSiblingReceiver A move row,
        (move.memberController A false).initial⟩,
      rightTemplate)
  obtain ⟨rightMove, hrightMove, hoperational⟩ :=
    profiledRawJointRecurrentOwnerFibreLeftEntry_operational_of_boundary A
      strategy hwin data hinvariant recurrentInput rightTemplate
  exact ⟨key, move, hread, rightMove, hrightMove, hoperational⟩

/-- Process-two mirror: a post-resolve target followed by any first recurrent
input enters the right-oriented operational owner-fibre carrier at the bank
root returned by finite readback. -/
theorem
    profiledRawJointStrictRightPostResolveLinkedMovePlay_operational_exists
    (initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy)
    (entry input recurrentInput : In₁ × In₂)
    (member : Bool) (env : Nat → In₁ × In₂) (n : Nat)
    (row : PairedEntryRow)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A) :
    let play := profiledRawJointStrictRightPostResolveLinkedMovePlay A strategy
      hwin initial entry input member env
    let projected := BlockRecordMonitor.projectReceiverPlay
      (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A)
      play
    let delivered :=
      (((projected n).2.1.target row).1,
        (profiledRawJointHybridFinitePayloadLinkedTargetPayload A
          ((projected n).2.1.target row)) member)
    ∃ (key : RootKey A strategy)
        (move : ProfiledRawJointRightPhysicalSiblingMove A),
      profiledRawJointOneSidedPhysicalCompatibleRootKey? A strategy
          delivered = some key ∧
        let data :
            ProfiledRawJointRecurrentRightBoundaryData A strategy hwin :=
          (profiledRawJointOneSidedPhysicalCompatibleBankRoot A strategy hwin
              key,
            ⟨initialProfiledRawJointRightPhysicalSiblingReceiver A move row,
              (move.memberController A false).initial⟩,
            leftTemplate)
        let packet :=
          profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A
            strategy hwin data.1 (data.target A strategy hwin recurrentInput)
        ∃ leftMove : ProfiledRawJointLeftPhysicalSiblingMove A,
          packet.successor.2.1.2.2 = some leftMove ∧
            ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy
              hwin
              (profiledRawJointRecurrentOwnerFibreRightEntryOne A strategy hwin
                data.1 (data.receiver A strategy hwin)
                  (data.owner A strategy hwin) leftTemplate packet)
              (profiledRawJointRecurrentOwnerFibreRightEntryTwo A strategy hwin
                data.1 (data.receiver A strategy hwin) packet) := by
  dsimp only
  obtain ⟨key, move, hread, hinvariant⟩ :=
    profiledRawJointStrictRightPostResolveLinkedMovePlay_rightBoundary_readback_exists
      A strategy hwin initial entry input member env n row leftTemplate
  let data : ProfiledRawJointRecurrentRightBoundaryData A strategy hwin :=
    (profiledRawJointOneSidedPhysicalCompatibleBankRoot A strategy hwin key,
      ⟨initialProfiledRawJointRightPhysicalSiblingReceiver A move row,
        (move.memberController A false).initial⟩,
      leftTemplate)
  obtain ⟨leftMove, hleftMove, hoperational⟩ :=
    profiledRawJointRecurrentOwnerFibreRightEntry_operational_of_boundary A
      strategy hwin data hinvariant recurrentInput leftTemplate
  exact ⟨key, move, hread, leftMove, hleftMove, hoperational⟩

end

end DetParityAutomaton

end DistributedSynthesis
