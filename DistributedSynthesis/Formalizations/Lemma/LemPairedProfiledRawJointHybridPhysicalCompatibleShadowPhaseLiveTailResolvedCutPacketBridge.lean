/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailRootAlignedCutStream

/-!
# Resolved cuts as root-aligned physical packets

The strengthened successor key retains the exact root-aligned tail transition,
whereas `TailResolvedCut` computes the physical block minimum and next DPA
state.  This file joins those two outputs without forgetting the common root.

The wrappers are stated on the suffix of an actual finite-machine trace.  They
therefore also transport the state-relative DPA equations of `TailResolvedCut`
back to the global run.  The orientation equality is proof-side bookkeeping;
it is never supplied to an executable endpoint map.
-/

namespace DistributedSynthesis

universe u v x y s w

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

/-! ## Results retaining both the transition and the physical close -/

/-- Output of a right-table close.  The crossed left slot is retained as the
literal root of both the exact transition and the cut packet. -/
structure
    ProfiledRawJointHybridShadowPhaseLiveTailRightResolvedCutPacketResult
    (tag : Tag A strategy hwin)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (start : Nat) (cuts : Nat → Nat)
    (initialSide : IndexedLineageSide)
    (state : Nat → TailState A strategy hwin tag) (k : Nat)
    (closeMember : Bool) where
  slot : ProfiledRawLeftSlot A
  nextMove : ProfiledRawJointLeftPhysicalSiblingMove A
  nextMove_eq : (state (k + 1)).1.2.2 = some nextMove
  nextMove_source : nextMove.1.source = slot
  transition :
    ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedTransitionAt A strategy
      hwin tag (state k) (state (k + 1)) .left (.inr slot)
  packet :
    ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedPhysicalCutPacketAt A
      strategy hwin tag G outputOne outputTwo env start cuts initialSide state k
  packet_root : packet.root = .inr slot
  nextDPAState_eq :
    A.run (G.globalMachineTraceWord outputOne outputTwo env)
        (start + cuts (k + 1)) =
      pairedCodeStateForRow A
        (profiledRawJointCloseRowOfMember closeMember) slot.1.1

/-- Left-table mirror. -/
structure
    ProfiledRawJointHybridShadowPhaseLiveTailLeftResolvedCutPacketResult
    (tag : Tag A strategy hwin)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (start : Nat) (cuts : Nat → Nat)
    (initialSide : IndexedLineageSide)
    (state : Nat → TailState A strategy hwin tag) (k : Nat)
    (closeMember : Bool) where
  slot : ProfiledRawRightSlot A
  nextMove : ProfiledRawJointRightPhysicalSiblingMove A
  nextMove_eq : (state (k + 1)).1.2.1 = some nextMove
  nextMove_source : nextMove.1.source = slot
  transition :
    ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedTransitionAt A strategy
      hwin tag (state k) (state (k + 1)) .right (.inl slot)
  packet :
    ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedPhysicalCutPacketAt A
      strategy hwin tag G outputOne outputTwo env start cuts initialSide state k
  packet_root : packet.root = .inl slot
  nextDPAState_eq :
    A.run (G.globalMachineTraceWord outputOne outputTwo env)
        (start + cuts (k + 1)) =
      pairedCodeStateForRow A
        (profiledRawJointCloseRowOfMember closeMember) slot.1.1

/-! ## Right-table adapter -/

/-- Turn the literal/resolved right close into the packet consumed by a
root-aligned stream.  `hside` merely identifies the proof-side alternating
index at this cut with the crossed left root already present in `hkey`. -/
theorem profiledRawJointHybridShadowPhaseLiveTailRight_resolvedCutPacket
    (tag : Tag A strategy hwin)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (start : Nat) (cuts : Nat → Nat)
    (initialSide : IndexedLineageSide)
    (state : Nat → TailState A strategy hwin tag) (k : Nat)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (tableMember : Bool) (entryRow : PairedEntryRow) (closeMember : Bool)
    (localEnv : Nat → In₂ × In₁) (n : Nat)
    (owner : (move.memberController A false).Control)
    (monitorState :
      (profiledRawJointHybridShadowPhaseLiveTailSuccessorRightMonitor A
        strategy hwin (tag := tag) move false).State)
    (segment :
      ProfiledRawJointHybridShadowPhaseLiveTailRightLiteralPrefixAt A strategy
        hwin tag (state k) move tableMember entryRow localEnv owner monitorState
          (OmegaWord.drop
            (G.globalMachineTraceWord outputOne outputTwo env) start)
          (cuts k) n)
    (hgap : n = cuts (k + 1) - cuts k - 1)
    (hkey :
      let output :=
        (profiledRawJointHybridShadowPhaseLiveTailRightDecoratedPlay A strategy
          hwin tag (state k) move tableMember localEnv n).2.1
      let target := (output.target entryRow).1
      ProfiledRawJointHybridShadowPhaseLiveTailRightSuccessorKeyAt A strategy
        hwin (state k) (state (k + 1)) target.1)
    (hside :
      profiledRawJointHybridPhysicalCompatibleSideAfter initialSide (k + 2) =
        .left)
    (hcut : cuts k < cuts (k + 1))
    (hstate :
      A.run (G.globalMachineTraceWord outputOne outputTwo env)
          (start + cuts k) =
        pairedCodeStateForRow A entryRow move.1.source.1.1)
    (hclosing :
      OmegaWord.drop
          (OmegaWord.drop
            (G.globalMachineTraceWord outputOne outputTwo env) start)
          (cuts k) n =
        profiledRawJointTargetRightClosingRecordForMember closeMember entryRow
          (profiledRawJointTargetRightPhysicalLetter A
            (profiledRawJointHybridShadowPhaseLiveTailRightPhysicalPlay A
              strategy hwin tag (state k) move tableMember localEnv n))) :
    Nonempty
      (ProfiledRawJointHybridShadowPhaseLiveTailRightResolvedCutPacketResult A
        strategy hwin tag G outputOne outputTwo env start cuts initialSide state
          k closeMember) := by
  let word := G.globalMachineTraceWord outputOne outputTwo env
  let localWord := OmegaWord.drop word start
  dsimp only at hkey
  rcases hkey with ⟨slot, hlive, ⟨aligned⟩⟩
  have hlocalState :
      A.runFrom (A.run word start) localWord (cuts k) =
        pairedCodeStateForRow A entryRow move.1.source.1.1 := by
    calc
      A.runFrom (A.run word start) localWord (cuts k) =
          A.run word (start + cuts k) := by
        exact A.runFrom_drop A.initial word start (cuts k)
      _ = pairedCodeStateForRow A entryRow move.1.source.1.1 := hstate
  have resolved :=
    profiledRawJointHybridShadowPhaseLiveTailRight_resolvedCut A strategy hwin
      tag (state k) (state (k + 1)) move tableMember entryRow closeMember
        localEnv n owner monitorState (A.run word start) localWord cuts k segment
          hgap ⟨slot, hlive, ⟨aligned⟩⟩ hcut hlocalState hclosing
  rcases resolved with
    ⟨nextMove, hnextMove, _hallowed, hblockLocal, hnextLocal⟩
  obtain ⟨_sameMove, _hsameMove, hsource⟩ :=
    aligned.left_move_source A strategy hwin
  have hnextMoveValue : _sameMove = nextMove := by
    rw [hnextMove] at _hsameMove
    exact (Option.some.inj _hsameMove).symm
  subst _sameMove
  have hsequence :
      (fun j ↦ A.priority (A.runFrom (A.run word start) localWord j)) =
        (fun j ↦ A.priority (A.run word (start + j))) := by
    funext j
    exact congrArg A.priority (A.runFrom_drop A.initial word start j)
  have hblock :
      cutBlockMin (fun j ↦ A.priority (A.run word (start + j))) cuts k =
        profiledRawJointThreadRootPriority A (.inr slot) := by
    rw [← hsequence]
    simpa [hsource] using hblockLocal
  have hnextGlobal :
      A.run word (start + cuts (k + 1)) =
        pairedCodeStateForRow A
          (profiledRawJointCloseRowOfMember closeMember) slot.1.1 := by
    calc
      A.run word (start + cuts (k + 1)) =
          A.runFrom (A.run word start) localWord (cuts (k + 1)) := by
        exact (A.runFrom_drop A.initial word start (cuts (k + 1))).symm
      _ = pairedCodeStateForRow A
          (profiledRawJointCloseRowOfMember closeMember)
          nextMove.1.source.1.1 := hnextLocal
      _ = pairedCodeStateForRow A
          (profiledRawJointCloseRowOfMember closeMember) slot.1.1 := by
        rw [hsource]
  let packet :
      ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedPhysicalCutPacketAt A
        strategy hwin tag G outputOne outputTwo env start cuts initialSide state
          k :=
    { root := .inr slot
      transition := by simpa only [hside] using aligned
      blockMin_eq_rootPriority := hblock }
  exact ⟨
    { slot := slot
      nextMove := nextMove
      nextMove_eq := hnextMove
      nextMove_source := hsource
      transition := aligned
      packet := packet
      packet_root := rfl
      nextDPAState_eq := hnextGlobal }⟩

/-! ## Left-table adapter -/

/-- Left-table mirror of
`profiledRawJointHybridShadowPhaseLiveTailRight_resolvedCutPacket`. -/
theorem profiledRawJointHybridShadowPhaseLiveTailLeft_resolvedCutPacket
    (tag : Tag A strategy hwin)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (start : Nat) (cuts : Nat → Nat)
    (initialSide : IndexedLineageSide)
    (state : Nat → TailState A strategy hwin tag) (k : Nat)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (tableMember : Bool) (entryRow : PairedEntryRow) (closeMember : Bool)
    (localEnv : Nat → In₁ × In₂) (n : Nat)
    (owner : (move.memberController A false).Control)
    (monitorState :
      (profiledRawJointHybridShadowPhaseLiveTailSuccessorLeftMonitor A strategy
        hwin (tag := tag) move false).State)
    (segment :
      ProfiledRawJointHybridShadowPhaseLiveTailLeftLiteralPrefixAt A strategy
        hwin tag (state k) move tableMember entryRow localEnv owner monitorState
          (OmegaWord.drop
            (G.globalMachineTraceWord outputOne outputTwo env) start)
          (cuts k) n)
    (hgap : n = cuts (k + 1) - cuts k - 1)
    (hkey :
      let output :=
        (profiledRawJointHybridShadowPhaseLiveTailLeftDecoratedPlay A strategy
          hwin tag (state k) move tableMember localEnv n).2.1
      let target := (output.target entryRow).1
      ProfiledRawJointHybridShadowPhaseLiveTailLeftSuccessorKeyAt A strategy
        hwin (state k) (state (k + 1)) target.1)
    (hside :
      profiledRawJointHybridPhysicalCompatibleSideAfter initialSide (k + 2) =
        .right)
    (hcut : cuts k < cuts (k + 1))
    (hstate :
      A.run (G.globalMachineTraceWord outputOne outputTwo env)
          (start + cuts k) =
        pairedCodeStateForRow A entryRow move.1.source.1.1)
    (hclosing :
      OmegaWord.drop
          (OmegaWord.drop
            (G.globalMachineTraceWord outputOne outputTwo env) start)
          (cuts k) n =
        profiledRawJointTargetLeftClosingRecordForMember closeMember entryRow
          (profiledRawJointTargetLeftPhysicalLetter A
            (profiledRawJointHybridShadowPhaseLiveTailLeftPhysicalPlay A
              strategy hwin tag (state k) move tableMember localEnv n))) :
    Nonempty
      (ProfiledRawJointHybridShadowPhaseLiveTailLeftResolvedCutPacketResult A
        strategy hwin tag G outputOne outputTwo env start cuts initialSide state
          k closeMember) := by
  let word := G.globalMachineTraceWord outputOne outputTwo env
  let localWord := OmegaWord.drop word start
  dsimp only at hkey
  rcases hkey with ⟨slot, hlive, ⟨aligned⟩⟩
  have hlocalState :
      A.runFrom (A.run word start) localWord (cuts k) =
        pairedCodeStateForRow A entryRow move.1.source.1.1 := by
    calc
      A.runFrom (A.run word start) localWord (cuts k) =
          A.run word (start + cuts k) := by
        exact A.runFrom_drop A.initial word start (cuts k)
      _ = pairedCodeStateForRow A entryRow move.1.source.1.1 := hstate
  have resolved :=
    profiledRawJointHybridShadowPhaseLiveTailLeft_resolvedCut A strategy hwin
      tag (state k) (state (k + 1)) move tableMember entryRow closeMember
        localEnv n owner monitorState (A.run word start) localWord cuts k segment
          hgap ⟨slot, hlive, ⟨aligned⟩⟩ hcut hlocalState hclosing
  rcases resolved with
    ⟨nextMove, hnextMove, _hallowed, hblockLocal, hnextLocal⟩
  obtain ⟨_sameMove, _hsameMove, hsource⟩ :=
    aligned.right_move_source A strategy hwin
  have hnextMoveValue : _sameMove = nextMove := by
    rw [hnextMove] at _hsameMove
    exact (Option.some.inj _hsameMove).symm
  subst _sameMove
  have hsequence :
      (fun j ↦ A.priority (A.runFrom (A.run word start) localWord j)) =
        (fun j ↦ A.priority (A.run word (start + j))) := by
    funext j
    exact congrArg A.priority (A.runFrom_drop A.initial word start j)
  have hblock :
      cutBlockMin (fun j ↦ A.priority (A.run word (start + j))) cuts k =
        profiledRawJointThreadRootPriority A (.inl slot) := by
    rw [← hsequence]
    simpa [hsource] using hblockLocal
  have hnextGlobal :
      A.run word (start + cuts (k + 1)) =
        pairedCodeStateForRow A
          (profiledRawJointCloseRowOfMember closeMember) slot.1.1 := by
    calc
      A.run word (start + cuts (k + 1)) =
          A.runFrom (A.run word start) localWord (cuts (k + 1)) := by
        exact (A.runFrom_drop A.initial word start (cuts (k + 1))).symm
      _ = pairedCodeStateForRow A
          (profiledRawJointCloseRowOfMember closeMember)
          nextMove.1.source.1.1 := hnextLocal
      _ = pairedCodeStateForRow A
          (profiledRawJointCloseRowOfMember closeMember) slot.1.1 := by
        rw [hsource]
  let packet :
      ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedPhysicalCutPacketAt A
        strategy hwin tag G outputOne outputTwo env start cuts initialSide state
          k :=
    { root := .inl slot
      transition := by simpa only [hside] using aligned
      blockMin_eq_rootPriority := hblock }
  exact ⟨
    { slot := slot
      nextMove := nextMove
      nextMove_eq := hnextMove
      nextMove_source := hsource
      transition := aligned
      packet := packet
      packet_root := rfl
      nextDPAState_eq := hnextGlobal }⟩

end

end DetParityAutomaton

end DistributedSynthesis
