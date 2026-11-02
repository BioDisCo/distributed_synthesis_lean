/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridFinitePayloadLinkedSiblingMove
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointTargetPhysicalPriority
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointAlignedCanonicalPhysicalSchedule

/-!
# Physical block minima for payload-linked tables

The finite payload and row proof attached before narrowing do not alter the
physical receiver letter or the profiled projection of its target.  Therefore
the existing target-parametric physical-priority theorem applies after the
single canonical receiver-output projection.

These lemmas are deliberately generic in the payload, allowed set, and play.
They can be used by the marked-bank table, the full-restart controller, or any
later finite payload carrier.  They assume only that the row-exact linked
monitor wins; no operational cut, graph side, hierarchy bit, leader bit, trace
equality, or semantic representative is involved.
-/

namespace DistributedSynthesis

universe u v x y s p

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

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- A winning row-exact right payload table carries the minimum priority of
its literal physical prefix in the profiled projection of every emitted
target. -/
theorem
    profiledRawJointHybridFinitePayloadRowExactRight_targetPriority_eq_blockMin_of_wins
    {Payload : Type p} [Fintype Payload]
    (Allowed :
      ProfiledRawJointHybridFinitePayloadLinkedTarget A Payload → Prop)
    (source : ProfiledRawRightSlot A)
    (linkedPlay : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRawJointHybridFinitePayloadRowExactRightReceiverOutput A
        Payload) Out₁)
    (hwin :
      (profiledRawJointHybridFinitePayloadRowExactRightBlockMonitor A Allowed
        source).WinsPlay linkedPlay)
    (n : Nat) (row : PairedEntryRow) :
    let play := BlockRecordMonitor.projectReceiverPlay
      (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A)
      linkedPlay
    pairedProfiledEntryPriority A
        (profiledRawJointHybridFinitePayloadLinkedRightTargetProjection A
          ((play n).2.1.target row)) =
      A.priority
        (blockMinState A
          (pairedCodeStateForRow A row source.1.1)
          (profiledRawJointTargetRightPhysicalPrefixRecords A row
            (omegaPrefix play n))) := by
  dsimp only
  let play := BlockRecordMonitor.projectReceiverPlay
    (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A)
    linkedPlay
  have hprojected :
      (profiledRawJointTargetRightBlockMonitor A
        (ProfiledRawJointHybridFinitePayloadLinkedTarget A Payload)
        (profiledRawJointHybridFinitePayloadLinkedRightTargetProjection A)
        Allowed source).WinsPlay play :=
    (BlockRecordMonitor.comapReceiverOutput_wins_iff
      (profiledRawJointTargetRightBlockMonitor A
        (ProfiledRawJointHybridFinitePayloadLinkedTarget A Payload)
        (profiledRawJointHybridFinitePayloadLinkedRightTargetProjection A)
        Allowed source)
      (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A)
      linkedPlay).mp hwin
  exact
    profiledRawJointTargetRight_targetPriority_eq_blockMin_of_wins A
      (profiledRawJointHybridFinitePayloadLinkedRightTargetProjection A)
      Allowed source play hprojected n row

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Left-table mirror of the payload-linked physical-priority projection. -/
theorem
    profiledRawJointHybridFinitePayloadRowExactLeft_targetPriority_eq_blockMin_of_wins
    {Payload : Type p} [Fintype Payload]
    (Allowed :
      ProfiledRawJointHybridFinitePayloadLinkedTarget A Payload → Prop)
    (source : ProfiledRawLeftSlot A)
    (linkedPlay : Nat → RealizedBlockRound In₁ In₂
      (ProfiledRawJointHybridFinitePayloadRowExactLeftReceiverOutput A
        Payload) Out₂)
    (hwin :
      (profiledRawJointHybridFinitePayloadRowExactLeftBlockMonitor A Allowed
        source).WinsPlay linkedPlay)
    (n : Nat) (row : PairedEntryRow) :
    let play := BlockRecordMonitor.projectReceiverPlay
      (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A)
      linkedPlay
    pairedProfiledEntryPriority A
        (profiledRawJointHybridFinitePayloadLinkedLeftTargetProjection A
          ((play n).2.1.target row)) =
      A.priority
        (blockMinState A
          (pairedCodeStateForRow A row source.1.1)
          (profiledRawJointTargetLeftPhysicalPrefixRecords A row
            (omegaPrefix play n))) := by
  dsimp only
  let play := BlockRecordMonitor.projectReceiverPlay
    (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A)
    linkedPlay
  have hprojected :
      (profiledRawJointTargetLeftBlockMonitor A
        (ProfiledRawJointHybridFinitePayloadLinkedTarget A Payload)
        (profiledRawJointHybridFinitePayloadLinkedLeftTargetProjection A)
        Allowed source).WinsPlay play :=
    (BlockRecordMonitor.comapReceiverOutput_wins_iff
      (profiledRawJointTargetLeftBlockMonitor A
        (ProfiledRawJointHybridFinitePayloadLinkedTarget A Payload)
        (profiledRawJointHybridFinitePayloadLinkedLeftTargetProjection A)
        Allowed source)
      (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A)
      linkedPlay).mp hwin
  exact
    profiledRawJointTargetLeft_targetPriority_eq_blockMin_of_wins A
      (profiledRawJointHybridFinitePayloadLinkedLeftTargetProjection A)
      Allowed source play hprojected n row

/-! ## Complete target packets

The priority projection above is enough for parity once entry-state alignment
has been established separately.  The persistent FullRestart induction also
needs to propagate that alignment from one cut to the next, so retain the
fresh target state supplied by the same projected monitor run. -/

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- A row-exact right payload table supplies both the fresh next-cut state and
the minimum priority of the block it just closed. -/
theorem
    profiledRawJointHybridFinitePayloadRowExactRight_freshState_and_blockPriority_of_wins
    {Payload : Type p} [Fintype Payload]
    (Allowed :
      ProfiledRawJointHybridFinitePayloadLinkedTarget A Payload → Prop)
    (source : ProfiledRawRightSlot A)
    (linkedPlay : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRawJointHybridFinitePayloadRowExactRightReceiverOutput A
        Payload) Out₁)
    (hwin :
      (profiledRawJointHybridFinitePayloadRowExactRightBlockMonitor A Allowed
        source).WinsPlay linkedPlay)
    (n : Nat) (row : PairedEntryRow) (slot : ProfiledRawLeftSlot A)
    (htarget :
      profiledRawJointHybridFinitePayloadLinkedRightTargetProjection A
          ((BlockRecordMonitor.projectReceiverPlay
            (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection
              A) linkedPlay n).2.1.target row) =
        .inr (.inr slot)) :
    let play := BlockRecordMonitor.projectReceiverPlay
      (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A)
      linkedPlay
    pairedCodeStateForRow A .first slot.1.1 =
          (pairedRightScanPairForRow A row
            (pairedRightScanStep A
              ((profiledRawJointTargetRightBlockMonitor A
                (ProfiledRawJointHybridFinitePayloadLinkedTarget A Payload)
                (profiledRawJointHybridFinitePayloadLinkedRightTargetProjection
                  A) Allowed source).run play n).2.1
              (profiledRawJointTargetRightPhysicalLetter A (play n)))).1 ∧
      profiledRawJointThreadRootPriority A (.inr slot) =
        A.priority
          (blockMinState A
            (pairedCodeStateForRow A row source.1.1)
            (profiledRawJointTargetRightPhysicalPrefixRecords A row
              (omegaPrefix play n))) := by
  dsimp only
  let play := BlockRecordMonitor.projectReceiverPlay
    (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A)
    linkedPlay
  have hprojected :
      (profiledRawJointTargetRightBlockMonitor A
        (ProfiledRawJointHybridFinitePayloadLinkedTarget A Payload)
        (profiledRawJointHybridFinitePayloadLinkedRightTargetProjection A)
        Allowed source).WinsPlay play :=
    (BlockRecordMonitor.comapReceiverOutput_wins_iff
      (profiledRawJointTargetRightBlockMonitor A
        (ProfiledRawJointHybridFinitePayloadLinkedTarget A Payload)
        (profiledRawJointHybridFinitePayloadLinkedRightTargetProjection A)
        Allowed source)
      (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A)
      linkedPlay).mp hwin
  exact
    profiledRawJointTargetRight_freshState_and_blockPriority_of_wins A
      (profiledRawJointHybridFinitePayloadLinkedRightTargetProjection A)
      Allowed source play hprojected n row slot htarget

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Left-table mirror of the complete target packet. -/
theorem
    profiledRawJointHybridFinitePayloadRowExactLeft_freshState_and_blockPriority_of_wins
    {Payload : Type p} [Fintype Payload]
    (Allowed :
      ProfiledRawJointHybridFinitePayloadLinkedTarget A Payload → Prop)
    (source : ProfiledRawLeftSlot A)
    (linkedPlay : Nat → RealizedBlockRound In₁ In₂
      (ProfiledRawJointHybridFinitePayloadRowExactLeftReceiverOutput A
        Payload) Out₂)
    (hwin :
      (profiledRawJointHybridFinitePayloadRowExactLeftBlockMonitor A Allowed
        source).WinsPlay linkedPlay)
    (n : Nat) (row : PairedEntryRow) (slot : ProfiledRawRightSlot A)
    (htarget :
      profiledRawJointHybridFinitePayloadLinkedLeftTargetProjection A
          ((BlockRecordMonitor.projectReceiverPlay
            (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection
              A) linkedPlay n).2.1.target row) =
        .inr (.inl slot)) :
    let play := BlockRecordMonitor.projectReceiverPlay
      (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A)
      linkedPlay
    pairedCodeStateForRow A .first slot.1.1 =
          (pairedLeftScanPairForRow A row
            (pairedLeftScanStep A
              ((profiledRawJointTargetLeftBlockMonitor A
                (ProfiledRawJointHybridFinitePayloadLinkedTarget A Payload)
                (profiledRawJointHybridFinitePayloadLinkedLeftTargetProjection
                  A) Allowed source).run play n).2.1
              (profiledRawJointTargetLeftPhysicalLetter A (play n)))).1 ∧
      profiledRawJointThreadRootPriority A (.inl slot) =
        A.priority
          (blockMinState A
            (pairedCodeStateForRow A row source.1.1)
            (profiledRawJointTargetLeftPhysicalPrefixRecords A row
              (omegaPrefix play n))) := by
  dsimp only
  let play := BlockRecordMonitor.projectReceiverPlay
    (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A)
    linkedPlay
  have hprojected :
      (profiledRawJointTargetLeftBlockMonitor A
        (ProfiledRawJointHybridFinitePayloadLinkedTarget A Payload)
        (profiledRawJointHybridFinitePayloadLinkedLeftTargetProjection A)
        Allowed source).WinsPlay play :=
    (BlockRecordMonitor.comapReceiverOutput_wins_iff
      (profiledRawJointTargetLeftBlockMonitor A
        (ProfiledRawJointHybridFinitePayloadLinkedTarget A Payload)
        (profiledRawJointHybridFinitePayloadLinkedLeftTargetProjection A)
        Allowed source)
      (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A)
      linkedPlay).mp hwin
  exact
    profiledRawJointTargetLeft_freshState_and_blockPriority_of_wins A
      (profiledRawJointHybridFinitePayloadLinkedLeftTargetProjection A)
      Allowed source play hprojected n row slot htarget

end

end DetParityAutomaton

end DistributedSynthesis
