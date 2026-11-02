/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointAlignedCanonicalPhysicalSchedule
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailDecoration

/-!
# Physical cut packets inside one delayed-tag tail fibre

The receiver decoration below a delayed tag changes only the finite successor
key carried by a table cell.  Its physical projection is therefore still a
winning play of the original right/left block monitor.  This file records the
consequence needed by the final trace induction: an exact literal prefix and
one closing record determine both the minimum priority of the physical block
and the DPA state at the next cut.

Unlike the older compatible-successor packet, these statements are indexed by
the re-rooted `TailState` itself.  No cast to a common-root policy occurs, and
the table member, old entry row, and fresh close member remain independent.
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

private abbrev Tag :=
  ProfiledRawJointHybridShadowPhaseLiveTag A strategy hwin

private abbrev TailState (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailState A strategy hwin tag

/-! ## Right-table play and projection -/

/-- The row-exact decorated play of one right table in a fixed tag fibre. -/
noncomputable def
    profiledRawJointHybridShadowPhaseLiveTailRightDecoratedPlay
    (tag : Tag A strategy hwin) (state : TailState A strategy hwin tag)
    (move : ProfiledRawJointRightPhysicalSiblingMove A) (member : Bool)
    (env : Nat → In₂ × In₁) :=
  let monitor :=
    profiledRawJointHybridShadowPhaseLiveTailSuccessorRightMonitor A strategy
      hwin (tag := tag) move member
  let controller :=
    profiledRawJointHybridShadowPhaseLiveTailDecoratedRightMemberController A
      strategy hwin state move member
  treePlay (narrowedInducedTree monitor controller.labeledTree) env

/-- Erase the tail key while retaining the literal physical table play. -/
noncomputable def
    profiledRawJointHybridShadowPhaseLiveTailRightPhysicalPlay
    (tag : Tag A strategy hwin) (state : TailState A strategy hwin tag)
    (move : ProfiledRawJointRightPhysicalSiblingMove A) (member : Bool)
    (env : Nat → In₂ × In₁) :=
  BlockRecordMonitor.projectReceiverPlay
    (profiledRawJointHybridShadowPhaseLiveTailRightReceiverProjection A
      strategy hwin (tag := tag))
    (profiledRawJointHybridShadowPhaseLiveTailRightDecoratedPlay A strategy
      hwin tag state move member env)

/-- The projected right play still wins the original physical monitor. -/
theorem profiledRawJointHybridShadowPhaseLiveTailRightPhysicalPlay_wins
    (tag : Tag A strategy hwin) (state : TailState A strategy hwin tag)
    (move : ProfiledRawJointRightPhysicalSiblingMove A) (member : Bool)
    (env : Nat → In₂ × In₁) :
    (profiledRawJointRightPhysicalSiblingMonitor A move.1 member).WinsPlay
      (profiledRawJointHybridShadowPhaseLiveTailRightPhysicalPlay A strategy
        hwin tag state move member env) := by
  let monitor :=
    profiledRawJointHybridShadowPhaseLiveTailSuccessorRightMonitor A strategy
      hwin (tag := tag) move member
  let controller :=
    profiledRawJointHybridShadowPhaseLiveTailDecoratedRightMemberController A
      strategy hwin state move member
  let play := treePlay
    (narrowedInducedTree monitor controller.labeledTree) env
  have htree : monitor.lift.WinningTree
      (narrowedInducedTree monitor controller.labeledTree) :=
    narrowedInducedTree_winningTree_of_allThreadsWin monitor
      (profiledRawJointHybridShadowPhaseLiveTailDecoratedRightMemberController_wins
        A strategy hwin state move member)
  have hplay : monitor.WinsPlay play :=
    (monitor.lift_winningTree_iff
      (narrowedInducedTree monitor controller.labeledTree)).mp htree env
  exact (BlockRecordMonitor.comapReceiverOutput_wins_iff
    (profiledRawJointRightPhysicalSiblingMonitor A move.1 member)
    (profiledRawJointHybridShadowPhaseLiveTailRightReceiverProjection A
      strategy hwin (tag := tag)) play).mp hplay

/-- An exact successor key already contains the live slot needed by the
physical monitor projection.  This is the small bridge between recursive tail
closure and the literal cut packet below. -/
theorem
    profiledRawJointHybridShadowPhaseLiveTailRightPhysicalTarget_of_key
    (tag : Tag A strategy hwin) (state next : TailState A strategy hwin tag)
    (move : ProfiledRawJointRightPhysicalSiblingMove A) (member : Bool)
    (env : Nat → In₂ × In₁) (n : Nat) (row : PairedEntryRow)
    (hkey :
      let output :=
        (profiledRawJointHybridShadowPhaseLiveTailRightDecoratedPlay A strategy
          hwin tag state move member env n).2.1
      ProfiledRawJointHybridShadowPhaseLiveTailRightSuccessorKeyAt A strategy
        hwin state next (output.target row).1.1) :
    ∃ slot : ProfiledRawLeftSlot A,
      ((profiledRawJointHybridShadowPhaseLiveTailRightDecoratedPlay A strategy
          hwin tag state move member env n).2.1.target row).1.1.family.left () =
          some slot ∧
        profiledRawJointUnitRightTargetProjection A
            ((profiledRawJointHybridShadowPhaseLiveTailRightPhysicalPlay A
              strategy hwin tag state move member env n).2.1.target row) =
          .inr (.inr slot) ∧
        tag.TailAllowedTarget A strategy hwin state next := by
  dsimp only at hkey
  rcases hkey with ⟨slot, hlive, htransition⟩
  refine ⟨slot, hlive, ?_, ?_⟩
  · change
      profiledRawJointUnitRightTargetProjection A
          (((profiledRawJointHybridShadowPhaseLiveTailRightDecoratedPlay A
            strategy hwin tag state move member env n).2.1.target row).1.1) =
        .inr (.inr slot)
    simp [profiledRawJointUnitRightTargetProjection, hlive]
  · exact
      ProfiledRawJointHybridShadowPhaseLiveTailRightSuccessorKeyAt.allowed A
        strategy hwin ⟨slot, hlive, htransition⟩

/-! ## Right member cut packet -/

/-- A right live-table block gives the physical minimum and exact next DPA
coordinate.  The three Boolean/row parameters are intentionally unrelated:
`tableMember` chose the installed table, `entryRow` chose its current thread,
and `closeMember` chooses only the fresh closing record/next row. -/
theorem profiledRawJointHybridShadowPhaseLiveTailRight_memberCutPacket
    (tag : Tag A strategy hwin) (state : TailState A strategy hwin tag)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (tableMember : Bool) (entryRow : PairedEntryRow) (closeMember : Bool)
    (env : Nat → In₂ × In₁) (n : Nat)
    (slot : ProfiledRawLeftSlot A)
    (htarget :
      profiledRawJointUnitRightTargetProjection A
          ((profiledRawJointHybridShadowPhaseLiveTailRightPhysicalPlay A
            strategy hwin tag state move tableMember env n).2.1.target
              entryRow) =
        .inr (.inr slot))
    (physicalState : A.State)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (cuts : Nat → Nat) (k : Nat)
    (hcut : cuts k < cuts (k + 1))
    (hstate : A.runFrom physicalState word (cuts k) =
      pairedCodeStateForRow A entryRow move.1.source.1.1)
    (hlength :
      (profiledRawJointTargetRightPhysicalPrefixRecords A entryRow
          (omegaPrefix
            (profiledRawJointHybridShadowPhaseLiveTailRightPhysicalPlay A
              strategy hwin tag state move tableMember env) n)).length =
        cuts (k + 1) - cuts k - 1)
    (hslice : omegaPrefix (OmegaWord.drop word (cuts k))
        (profiledRawJointTargetRightPhysicalPrefixRecords A entryRow
          (omegaPrefix
            (profiledRawJointHybridShadowPhaseLiveTailRightPhysicalPlay A
              strategy hwin tag state move tableMember env) n)).length =
      profiledRawJointTargetRightPhysicalPrefixRecords A entryRow
        (omegaPrefix
          (profiledRawJointHybridShadowPhaseLiveTailRightPhysicalPlay A
            strategy hwin tag state move tableMember env) n))
    (hclosing : OmegaWord.drop word (cuts k)
        (profiledRawJointTargetRightPhysicalPrefixRecords A entryRow
          (omegaPrefix
            (profiledRawJointHybridShadowPhaseLiveTailRightPhysicalPlay A
              strategy hwin tag state move tableMember env) n)).length =
      profiledRawJointTargetRightClosingRecordForMember closeMember entryRow
        (profiledRawJointTargetRightPhysicalLetter A
          (profiledRawJointHybridShadowPhaseLiveTailRightPhysicalPlay A
            strategy hwin tag state move tableMember env n))) :
    cutBlockMin
        (fun j ↦ A.priority (A.runFrom physicalState word j)) cuts k =
        profiledRawJointThreadRootPriority A (.inr slot) ∧
      A.runFrom physicalState word (cuts (k + 1)) =
        pairedCodeStateForRow A
          (profiledRawJointCloseRowOfMember closeMember) slot.1.1 := by
  let play :=
    profiledRawJointHybridShadowPhaseLiveTailRightPhysicalPlay A strategy hwin
      tag state move tableMember env
  have hwins :=
    profiledRawJointHybridShadowPhaseLiveTailRightPhysicalPlay_wins A strategy
      hwin tag state move tableMember env
  exact
    profiledRawJointTargetRight_memberCutPacket_of_wins A
      (profiledRawJointUnitRightTargetProjection A)
      (profiledRawJointRightPhysicalSiblingAllowed A move.1)
      move.1.source play hwins n entryRow slot htarget closeMember
      physicalState word cuts k hcut hstate hlength hslice hclosing

/-- The recursive successor-key proof and the physical cut proof are consumed
together.  This is the exact packet required at a right-oriented close of the
final tagged trace. -/
theorem profiledRawJointHybridShadowPhaseLiveTailRight_allowedMemberCutPacket
    (tag : Tag A strategy hwin) (state next : TailState A strategy hwin tag)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (tableMember : Bool) (entryRow : PairedEntryRow) (closeMember : Bool)
    (env : Nat → In₂ × In₁) (n : Nat)
    (hkey :
      let output :=
        (profiledRawJointHybridShadowPhaseLiveTailRightDecoratedPlay A strategy
          hwin tag state move tableMember env n).2.1
      ProfiledRawJointHybridShadowPhaseLiveTailRightSuccessorKeyAt A strategy
        hwin state next (output.target entryRow).1.1)
    (physicalState : A.State)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (cuts : Nat → Nat) (k : Nat)
    (hcut : cuts k < cuts (k + 1))
    (hstate : A.runFrom physicalState word (cuts k) =
      pairedCodeStateForRow A entryRow move.1.source.1.1)
    (hlength :
      (profiledRawJointTargetRightPhysicalPrefixRecords A entryRow
          (omegaPrefix
            (profiledRawJointHybridShadowPhaseLiveTailRightPhysicalPlay A
              strategy hwin tag state move tableMember env) n)).length =
        cuts (k + 1) - cuts k - 1)
    (hslice : omegaPrefix (OmegaWord.drop word (cuts k))
        (profiledRawJointTargetRightPhysicalPrefixRecords A entryRow
          (omegaPrefix
            (profiledRawJointHybridShadowPhaseLiveTailRightPhysicalPlay A
              strategy hwin tag state move tableMember env) n)).length =
      profiledRawJointTargetRightPhysicalPrefixRecords A entryRow
        (omegaPrefix
          (profiledRawJointHybridShadowPhaseLiveTailRightPhysicalPlay A
            strategy hwin tag state move tableMember env) n))
    (hclosing : OmegaWord.drop word (cuts k)
        (profiledRawJointTargetRightPhysicalPrefixRecords A entryRow
          (omegaPrefix
            (profiledRawJointHybridShadowPhaseLiveTailRightPhysicalPlay A
              strategy hwin tag state move tableMember env) n)).length =
      profiledRawJointTargetRightClosingRecordForMember closeMember entryRow
        (profiledRawJointTargetRightPhysicalLetter A
          (profiledRawJointHybridShadowPhaseLiveTailRightPhysicalPlay A
            strategy hwin tag state move tableMember env n))) :
    ∃ slot : ProfiledRawLeftSlot A,
      tag.TailAllowedTarget A strategy hwin state next ∧
        cutBlockMin
            (fun j ↦ A.priority (A.runFrom physicalState word j)) cuts k =
          profiledRawJointThreadRootPriority A (.inr slot) ∧
        A.runFrom physicalState word (cuts (k + 1)) =
          pairedCodeStateForRow A
            (profiledRawJointCloseRowOfMember closeMember) slot.1.1 := by
  obtain ⟨slot, _hlive, htarget, hallowed⟩ :=
    profiledRawJointHybridShadowPhaseLiveTailRightPhysicalTarget_of_key A
      strategy hwin tag state next move tableMember env n entryRow hkey
  have hphysical :=
    profiledRawJointHybridShadowPhaseLiveTailRight_memberCutPacket A strategy
      hwin tag state move tableMember entryRow closeMember env n slot htarget
        physicalState word cuts k hcut hstate hlength hslice hclosing
  exact ⟨slot, hallowed, hphysical.1, hphysical.2⟩

/-! ## Left-table mirror -/

noncomputable def
    profiledRawJointHybridShadowPhaseLiveTailLeftDecoratedPlay
    (tag : Tag A strategy hwin) (state : TailState A strategy hwin tag)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A) (member : Bool)
    (env : Nat → In₁ × In₂) :=
  let monitor :=
    profiledRawJointHybridShadowPhaseLiveTailSuccessorLeftMonitor A strategy
      hwin (tag := tag) move member
  let controller :=
    profiledRawJointHybridShadowPhaseLiveTailDecoratedLeftMemberController A
      strategy hwin state move member
  treePlay (narrowedInducedTree monitor controller.labeledTree) env

noncomputable def
    profiledRawJointHybridShadowPhaseLiveTailLeftPhysicalPlay
    (tag : Tag A strategy hwin) (state : TailState A strategy hwin tag)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A) (member : Bool)
    (env : Nat → In₁ × In₂) :=
  BlockRecordMonitor.projectReceiverPlay
    (profiledRawJointHybridShadowPhaseLiveTailLeftReceiverProjection A strategy
      hwin (tag := tag))
    (profiledRawJointHybridShadowPhaseLiveTailLeftDecoratedPlay A strategy hwin
      tag state move member env)

theorem profiledRawJointHybridShadowPhaseLiveTailLeftPhysicalPlay_wins
    (tag : Tag A strategy hwin) (state : TailState A strategy hwin tag)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A) (member : Bool)
    (env : Nat → In₁ × In₂) :
    (profiledRawJointLeftPhysicalSiblingMonitor A move.1 member).WinsPlay
      (profiledRawJointHybridShadowPhaseLiveTailLeftPhysicalPlay A strategy
        hwin tag state move member env) := by
  let monitor :=
    profiledRawJointHybridShadowPhaseLiveTailSuccessorLeftMonitor A strategy
      hwin (tag := tag) move member
  let controller :=
    profiledRawJointHybridShadowPhaseLiveTailDecoratedLeftMemberController A
      strategy hwin state move member
  let play := treePlay
    (narrowedInducedTree monitor controller.labeledTree) env
  have htree : monitor.lift.WinningTree
      (narrowedInducedTree monitor controller.labeledTree) :=
    narrowedInducedTree_winningTree_of_allThreadsWin monitor
      (profiledRawJointHybridShadowPhaseLiveTailDecoratedLeftMemberController_wins
        A strategy hwin state move member)
  have hplay : monitor.WinsPlay play :=
    (monitor.lift_winningTree_iff
      (narrowedInducedTree monitor controller.labeledTree)).mp htree env
  exact (BlockRecordMonitor.comapReceiverOutput_wins_iff
    (profiledRawJointLeftPhysicalSiblingMonitor A move.1 member)
    (profiledRawJointHybridShadowPhaseLiveTailLeftReceiverProjection A strategy
      hwin (tag := tag)) play).mp hplay

/-- Left mirror of the exact-key/physical-target bridge. -/
theorem
    profiledRawJointHybridShadowPhaseLiveTailLeftPhysicalTarget_of_key
    (tag : Tag A strategy hwin) (state next : TailState A strategy hwin tag)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A) (member : Bool)
    (env : Nat → In₁ × In₂) (n : Nat) (row : PairedEntryRow)
    (hkey :
      let output :=
        (profiledRawJointHybridShadowPhaseLiveTailLeftDecoratedPlay A strategy
          hwin tag state move member env n).2.1
      ProfiledRawJointHybridShadowPhaseLiveTailLeftSuccessorKeyAt A strategy
        hwin state next (output.target row).1.1) :
    ∃ slot : ProfiledRawRightSlot A,
      ((profiledRawJointHybridShadowPhaseLiveTailLeftDecoratedPlay A strategy
          hwin tag state move member env n).2.1.target row).1.1.family.right () =
          some slot ∧
        profiledRawJointUnitLeftTargetProjection A
            ((profiledRawJointHybridShadowPhaseLiveTailLeftPhysicalPlay A
              strategy hwin tag state move member env n).2.1.target row) =
          .inr (.inl slot) ∧
        tag.TailAllowedTarget A strategy hwin state next := by
  dsimp only at hkey
  rcases hkey with ⟨slot, hlive, htransition⟩
  refine ⟨slot, hlive, ?_, ?_⟩
  · change
      profiledRawJointUnitLeftTargetProjection A
          (((profiledRawJointHybridShadowPhaseLiveTailLeftDecoratedPlay A
            strategy hwin tag state move member env n).2.1.target row).1.1) =
        .inr (.inl slot)
    simp [profiledRawJointUnitLeftTargetProjection, hlive]
  · exact
      ProfiledRawJointHybridShadowPhaseLiveTailLeftSuccessorKeyAt.allowed A
        strategy hwin ⟨slot, hlive, htransition⟩

/-- Left mirror of the tag-relative three-parameter cut packet. -/
theorem profiledRawJointHybridShadowPhaseLiveTailLeft_memberCutPacket
    (tag : Tag A strategy hwin) (state : TailState A strategy hwin tag)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (tableMember : Bool) (entryRow : PairedEntryRow) (closeMember : Bool)
    (env : Nat → In₁ × In₂) (n : Nat)
    (slot : ProfiledRawRightSlot A)
    (htarget :
      profiledRawJointUnitLeftTargetProjection A
          ((profiledRawJointHybridShadowPhaseLiveTailLeftPhysicalPlay A strategy
            hwin tag state move tableMember env n).2.1.target entryRow) =
        .inr (.inl slot))
    (physicalState : A.State)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (cuts : Nat → Nat) (k : Nat)
    (hcut : cuts k < cuts (k + 1))
    (hstate : A.runFrom physicalState word (cuts k) =
      pairedCodeStateForRow A entryRow move.1.source.1.1)
    (hlength :
      (profiledRawJointTargetLeftPhysicalPrefixRecords A entryRow
          (omegaPrefix
            (profiledRawJointHybridShadowPhaseLiveTailLeftPhysicalPlay A
              strategy hwin tag state move tableMember env) n)).length =
        cuts (k + 1) - cuts k - 1)
    (hslice : omegaPrefix (OmegaWord.drop word (cuts k))
        (profiledRawJointTargetLeftPhysicalPrefixRecords A entryRow
          (omegaPrefix
            (profiledRawJointHybridShadowPhaseLiveTailLeftPhysicalPlay A
              strategy hwin tag state move tableMember env) n)).length =
      profiledRawJointTargetLeftPhysicalPrefixRecords A entryRow
        (omegaPrefix
          (profiledRawJointHybridShadowPhaseLiveTailLeftPhysicalPlay A strategy
            hwin tag state move tableMember env) n))
    (hclosing : OmegaWord.drop word (cuts k)
        (profiledRawJointTargetLeftPhysicalPrefixRecords A entryRow
          (omegaPrefix
            (profiledRawJointHybridShadowPhaseLiveTailLeftPhysicalPlay A
              strategy hwin tag state move tableMember env) n)).length =
      profiledRawJointTargetLeftClosingRecordForMember closeMember entryRow
        (profiledRawJointTargetLeftPhysicalLetter A
          (profiledRawJointHybridShadowPhaseLiveTailLeftPhysicalPlay A strategy
            hwin tag state move tableMember env n))) :
    cutBlockMin
        (fun j ↦ A.priority (A.runFrom physicalState word j)) cuts k =
        profiledRawJointThreadRootPriority A (.inl slot) ∧
      A.runFrom physicalState word (cuts (k + 1)) =
        pairedCodeStateForRow A
          (profiledRawJointCloseRowOfMember closeMember) slot.1.1 := by
  let play :=
    profiledRawJointHybridShadowPhaseLiveTailLeftPhysicalPlay A strategy hwin
      tag state move tableMember env
  have hwins :=
    profiledRawJointHybridShadowPhaseLiveTailLeftPhysicalPlay_wins A strategy
      hwin tag state move tableMember env
  exact
    profiledRawJointTargetLeft_memberCutPacket_of_wins A
      (profiledRawJointUnitLeftTargetProjection A)
      (profiledRawJointLeftPhysicalSiblingAllowed A move.1)
      move.1.source play hwins n entryRow slot htarget closeMember
      physicalState word cuts k hcut hstate hlength hslice hclosing

/-- Left-oriented recursive/physical packet. -/
theorem profiledRawJointHybridShadowPhaseLiveTailLeft_allowedMemberCutPacket
    (tag : Tag A strategy hwin) (state next : TailState A strategy hwin tag)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (tableMember : Bool) (entryRow : PairedEntryRow) (closeMember : Bool)
    (env : Nat → In₁ × In₂) (n : Nat)
    (hkey :
      let output :=
        (profiledRawJointHybridShadowPhaseLiveTailLeftDecoratedPlay A strategy
          hwin tag state move tableMember env n).2.1
      ProfiledRawJointHybridShadowPhaseLiveTailLeftSuccessorKeyAt A strategy
        hwin state next (output.target entryRow).1.1)
    (physicalState : A.State)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (cuts : Nat → Nat) (k : Nat)
    (hcut : cuts k < cuts (k + 1))
    (hstate : A.runFrom physicalState word (cuts k) =
      pairedCodeStateForRow A entryRow move.1.source.1.1)
    (hlength :
      (profiledRawJointTargetLeftPhysicalPrefixRecords A entryRow
          (omegaPrefix
            (profiledRawJointHybridShadowPhaseLiveTailLeftPhysicalPlay A
              strategy hwin tag state move tableMember env) n)).length =
        cuts (k + 1) - cuts k - 1)
    (hslice : omegaPrefix (OmegaWord.drop word (cuts k))
        (profiledRawJointTargetLeftPhysicalPrefixRecords A entryRow
          (omegaPrefix
            (profiledRawJointHybridShadowPhaseLiveTailLeftPhysicalPlay A
              strategy hwin tag state move tableMember env) n)).length =
      profiledRawJointTargetLeftPhysicalPrefixRecords A entryRow
        (omegaPrefix
          (profiledRawJointHybridShadowPhaseLiveTailLeftPhysicalPlay A strategy
            hwin tag state move tableMember env) n))
    (hclosing : OmegaWord.drop word (cuts k)
        (profiledRawJointTargetLeftPhysicalPrefixRecords A entryRow
          (omegaPrefix
            (profiledRawJointHybridShadowPhaseLiveTailLeftPhysicalPlay A
              strategy hwin tag state move tableMember env) n)).length =
      profiledRawJointTargetLeftClosingRecordForMember closeMember entryRow
        (profiledRawJointTargetLeftPhysicalLetter A
          (profiledRawJointHybridShadowPhaseLiveTailLeftPhysicalPlay A strategy
            hwin tag state move tableMember env n))) :
    ∃ slot : ProfiledRawRightSlot A,
      tag.TailAllowedTarget A strategy hwin state next ∧
        cutBlockMin
            (fun j ↦ A.priority (A.runFrom physicalState word j)) cuts k =
          profiledRawJointThreadRootPriority A (.inl slot) ∧
        A.runFrom physicalState word (cuts (k + 1)) =
          pairedCodeStateForRow A
            (profiledRawJointCloseRowOfMember closeMember) slot.1.1 := by
  obtain ⟨slot, _hlive, htarget, hallowed⟩ :=
    profiledRawJointHybridShadowPhaseLiveTailLeftPhysicalTarget_of_key A
      strategy hwin tag state next move tableMember env n entryRow hkey
  have hphysical :=
    profiledRawJointHybridShadowPhaseLiveTailLeft_memberCutPacket A strategy
      hwin tag state move tableMember entryRow closeMember env n slot htarget
        physicalState word cuts k hcut hstate hlength hslice hclosing
  exact ⟨slot, hallowed, hphysical.1, hphysical.2⟩

end

end DetParityAutomaton

end DistributedSynthesis
