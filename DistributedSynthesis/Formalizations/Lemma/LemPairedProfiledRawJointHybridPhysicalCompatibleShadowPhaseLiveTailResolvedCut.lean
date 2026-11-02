/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailLiteralPrefix
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailTransitionRootAlignment

/-!
# Resolved physical cuts in one delayed-tag tail fibre

A literal table prefix supplies the exact open block, a root-aligned decorated
target supplies both the allowed next tail key and the source of its installed
move, and the tag-relative member-cut packet supplies the physical minimum and
next DPA state.  Combining the three removes the intermediate target slot:
the next DPA state is stated directly at the move that will execute the next
block.

All scheduling facts remain explicit proof hypotheses.  No executable map in
this file receives a graph, orientation, hierarchy side, leader bit, or
history.
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

private abbrev PhysicalWord :=
  OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂)

/-! ## Root-aligned target keys -/

/-- The right-table target code, retained next key, and crossed live left root
are witnessed by one root-aligned exact transition. -/
def ProfiledRawJointHybridShadowPhaseLiveTailRightRootAlignedSuccessorKeyAt
    {tag : Tag A strategy hwin}
    (state next : TailState A strategy hwin tag)
    (target : ProfiledRawJointIncidenceCode A (I := Unit)) : Prop :=
  ∃ slot : ProfiledRawLeftSlot A,
    target.family.left () = some slot ∧
      Nonempty
        (ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedTransitionAt A
          strategy hwin tag state next .left (.inr slot))

/-- Left-table mirror. -/
def ProfiledRawJointHybridShadowPhaseLiveTailLeftRootAlignedSuccessorKeyAt
    {tag : Tag A strategy hwin}
    (state next : TailState A strategy hwin tag)
    (target : ProfiledRawJointIncidenceCode A (I := Unit)) : Prop :=
  ∃ slot : ProfiledRawRightSlot A,
    target.family.right () = some slot ∧
      Nonempty
        (ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedTransitionAt A
          strategy hwin tag state next .right (.inl slot))

/-! ## Right resolved cut -/

/-- One right-oriented literal block, closed through a root-aligned target.
The result is already normalized to the left move installed for the next
block. -/
theorem profiledRawJointHybridShadowPhaseLiveTailRight_resolvedCut
    (tag : Tag A strategy hwin)
    (state next : TailState A strategy hwin tag)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (tableMember : Bool) (entryRow : PairedEntryRow) (closeMember : Bool)
    (localEnv : Nat → In₂ × In₁) (n : Nat)
    (owner : (move.memberController A false).Control)
    (monitorState :
      (profiledRawJointHybridShadowPhaseLiveTailSuccessorRightMonitor A
        strategy hwin (tag := tag) move false).State)
    (physicalState : A.State)
    (word : PhysicalWord (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂))
    (cuts : Nat → Nat) (k : Nat)
    (segment :
      ProfiledRawJointHybridShadowPhaseLiveTailRightLiteralPrefixAt A strategy
        hwin tag state move tableMember entryRow localEnv owner monitorState word
          (cuts k) n)
    (hgap : n = cuts (k + 1) - cuts k - 1)
    (hkey :
      let output :=
        (profiledRawJointHybridShadowPhaseLiveTailRightDecoratedPlay A strategy
          hwin tag state move tableMember localEnv n).2.1
      let target := (output.target entryRow).1
      ProfiledRawJointHybridShadowPhaseLiveTailRightSuccessorKeyAt A strategy
        hwin state next target.1)
    (hcut : cuts k < cuts (k + 1))
    (hstate : A.runFrom physicalState word (cuts k) =
      pairedCodeStateForRow A entryRow move.1.source.1.1)
    (hclosing : OmegaWord.drop word (cuts k) n =
      profiledRawJointTargetRightClosingRecordForMember closeMember entryRow
        (profiledRawJointTargetRightPhysicalLetter A
          (profiledRawJointHybridShadowPhaseLiveTailRightPhysicalPlay A strategy
            hwin tag state move tableMember localEnv n))) :
    ∃ nextMove : ProfiledRawJointLeftPhysicalSiblingMove A,
      next.1.2.2 = some nextMove ∧
        tag.TailAllowedTarget A strategy hwin state next ∧
        cutBlockMin
            (fun j ↦ A.priority (A.runFrom physicalState word j)) cuts k =
          profiledRawJointThreadRootPriority A (.inr nextMove.1.source) ∧
        A.runFrom physicalState word (cuts (k + 1)) =
          pairedCodeStateForRow A
            (profiledRawJointCloseRowOfMember closeMember)
            nextMove.1.source.1.1 := by
  dsimp only at hkey
  rcases hkey with ⟨slot, hlive, ⟨aligned⟩⟩
  obtain ⟨nextMove, hnextMove, hsource⟩ :=
    aligned.left_move_source A strategy hwin
  have htarget :
      profiledRawJointUnitRightTargetProjection A
          ((profiledRawJointHybridShadowPhaseLiveTailRightPhysicalPlay A
            strategy hwin tag state move tableMember localEnv n).2.1.target
              entryRow) =
        .inr (.inr slot) := by
    simp [profiledRawJointHybridShadowPhaseLiveTailRightPhysicalPlay,
      BlockRecordMonitor.projectReceiverPlay,
      profiledRawJointHybridShadowPhaseLiveTailRightReceiverProjection,
      profiledRawJointUnitRightTargetProjection, hlive]
  obtain ⟨hlength, hslice⟩ := segment.cutPrefix A strategy hwin
  have hlength' :
      (profiledRawJointTargetRightPhysicalPrefixRecords A entryRow
        (omegaPrefix
          (profiledRawJointHybridShadowPhaseLiveTailRightPhysicalPlay A strategy
            hwin tag state move tableMember localEnv) n)).length =
        cuts (k + 1) - cuts k - 1 :=
    hlength.trans hgap
  have hclosing' :
      OmegaWord.drop word (cuts k)
          (profiledRawJointTargetRightPhysicalPrefixRecords A entryRow
            (omegaPrefix
              (profiledRawJointHybridShadowPhaseLiveTailRightPhysicalPlay A
                strategy hwin tag state move tableMember localEnv) n)).length =
        profiledRawJointTargetRightClosingRecordForMember closeMember entryRow
          (profiledRawJointTargetRightPhysicalLetter A
            (profiledRawJointHybridShadowPhaseLiveTailRightPhysicalPlay A
              strategy hwin tag state move tableMember localEnv n)) := by
    rw [hlength]
    exact hclosing
  have packet :=
    profiledRawJointHybridShadowPhaseLiveTailRight_memberCutPacket A strategy
      hwin tag state move tableMember entryRow closeMember localEnv n slot
        htarget physicalState word cuts k hcut hstate hlength' hslice hclosing'
  refine ⟨nextMove, hnextMove, aligned.allowed A strategy hwin, ?_, ?_⟩
  · simpa [hsource] using packet.1
  · simpa [hsource] using packet.2

/-! ## Left resolved cut -/

/-- Left-oriented mirror, normalized to the right move installed for the next
block. -/
theorem profiledRawJointHybridShadowPhaseLiveTailLeft_resolvedCut
    (tag : Tag A strategy hwin)
    (state next : TailState A strategy hwin tag)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (tableMember : Bool) (entryRow : PairedEntryRow) (closeMember : Bool)
    (localEnv : Nat → In₁ × In₂) (n : Nat)
    (owner : (move.memberController A false).Control)
    (monitorState :
      (profiledRawJointHybridShadowPhaseLiveTailSuccessorLeftMonitor A strategy
        hwin (tag := tag) move false).State)
    (physicalState : A.State)
    (word : PhysicalWord (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂))
    (cuts : Nat → Nat) (k : Nat)
    (segment :
      ProfiledRawJointHybridShadowPhaseLiveTailLeftLiteralPrefixAt A strategy
        hwin tag state move tableMember entryRow localEnv owner monitorState word
          (cuts k) n)
    (hgap : n = cuts (k + 1) - cuts k - 1)
    (hkey :
      let output :=
        (profiledRawJointHybridShadowPhaseLiveTailLeftDecoratedPlay A strategy
          hwin tag state move tableMember localEnv n).2.1
      let target := (output.target entryRow).1
      ProfiledRawJointHybridShadowPhaseLiveTailLeftSuccessorKeyAt A strategy
        hwin state next target.1)
    (hcut : cuts k < cuts (k + 1))
    (hstate : A.runFrom physicalState word (cuts k) =
      pairedCodeStateForRow A entryRow move.1.source.1.1)
    (hclosing : OmegaWord.drop word (cuts k) n =
      profiledRawJointTargetLeftClosingRecordForMember closeMember entryRow
        (profiledRawJointTargetLeftPhysicalLetter A
          (profiledRawJointHybridShadowPhaseLiveTailLeftPhysicalPlay A strategy
            hwin tag state move tableMember localEnv n))) :
    ∃ nextMove : ProfiledRawJointRightPhysicalSiblingMove A,
      next.1.2.1 = some nextMove ∧
        tag.TailAllowedTarget A strategy hwin state next ∧
        cutBlockMin
            (fun j ↦ A.priority (A.runFrom physicalState word j)) cuts k =
          profiledRawJointThreadRootPriority A (.inl nextMove.1.source) ∧
        A.runFrom physicalState word (cuts (k + 1)) =
          pairedCodeStateForRow A
            (profiledRawJointCloseRowOfMember closeMember)
            nextMove.1.source.1.1 := by
  dsimp only at hkey
  rcases hkey with ⟨slot, hlive, ⟨aligned⟩⟩
  obtain ⟨nextMove, hnextMove, hsource⟩ :=
    aligned.right_move_source A strategy hwin
  have htarget :
      profiledRawJointUnitLeftTargetProjection A
          ((profiledRawJointHybridShadowPhaseLiveTailLeftPhysicalPlay A strategy
            hwin tag state move tableMember localEnv n).2.1.target entryRow) =
        .inr (.inl slot) := by
    simp [profiledRawJointHybridShadowPhaseLiveTailLeftPhysicalPlay,
      BlockRecordMonitor.projectReceiverPlay,
      profiledRawJointHybridShadowPhaseLiveTailLeftReceiverProjection,
      profiledRawJointUnitLeftTargetProjection, hlive]
  obtain ⟨hlength, hslice⟩ := segment.cutPrefix A strategy hwin
  have hlength' :
      (profiledRawJointTargetLeftPhysicalPrefixRecords A entryRow
        (omegaPrefix
          (profiledRawJointHybridShadowPhaseLiveTailLeftPhysicalPlay A strategy
            hwin tag state move tableMember localEnv) n)).length =
        cuts (k + 1) - cuts k - 1 :=
    hlength.trans hgap
  have hclosing' :
      OmegaWord.drop word (cuts k)
          (profiledRawJointTargetLeftPhysicalPrefixRecords A entryRow
            (omegaPrefix
              (profiledRawJointHybridShadowPhaseLiveTailLeftPhysicalPlay A
                strategy hwin tag state move tableMember localEnv) n)).length =
        profiledRawJointTargetLeftClosingRecordForMember closeMember entryRow
          (profiledRawJointTargetLeftPhysicalLetter A
            (profiledRawJointHybridShadowPhaseLiveTailLeftPhysicalPlay A strategy
              hwin tag state move tableMember localEnv n)) := by
    rw [hlength]
    exact hclosing
  have packet :=
    profiledRawJointHybridShadowPhaseLiveTailLeft_memberCutPacket A strategy hwin
      tag state move tableMember entryRow closeMember localEnv n slot htarget
        physicalState word cuts k hcut hstate hlength' hslice hclosing'
  refine ⟨nextMove, hnextMove, aligned.allowed A strategy hwin, ?_, ?_⟩
  · simpa [hsource] using packet.1
  · simpa [hsource] using packet.2

end

end DetParityAutomaton

end DistributedSynthesis
