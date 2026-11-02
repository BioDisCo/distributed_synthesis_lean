/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailSingleTableSeed
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailSingleTableBoth

/-!
# The recurrent one-table alignment invariant

The canonical owner and receiver installed at a tail key are aligned because
both are computed from the same optional move in that key.  Exact target
transitions preserve the premise through their `child_move` field.  Ordinary
local evolution retains the key and move on both endpoints, so it preserves
the alignment relation as well.

Every function in this file consumes only finite carrier data.  Side names
index the two statically typed handlers; no function inspects a graph,
orientation, leader bit, strict-leader bit, history, or semantic view.
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

private abbrev RightOwner (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailFrontierOneShared A strategy hwin
    tag

private abbrev LeftOwner (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailFrontierTwoShared A strategy hwin
    tag

private abbrev RightReceiver (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailRightReceiver A strategy hwin tag

private abbrev LeftReceiver (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailLeftReceiver A strategy hwin tag

/-! ## Canonical aligned endpoints at a key -/

noncomputable def profiledRawJointHybridShadowPhaseLiveTailRightSeedOwner
    (tag : Tag A strategy hwin) (state : TailState A strategy hwin tag) :
    RightOwner A strategy hwin tag :=
  ⟨state,
    profiledRawJointHybridShadowPhaseLiveTailRightSharedInitial A strategy hwin
      tag state⟩

noncomputable def profiledRawJointHybridShadowPhaseLiveTailLeftSeedOwner
    (tag : Tag A strategy hwin) (state : TailState A strategy hwin tag) :
    LeftOwner A strategy hwin tag :=
  ⟨state,
    profiledRawJointHybridShadowPhaseLiveTailLeftSharedInitial A strategy hwin
      tag state⟩

noncomputable def profiledRawJointHybridShadowPhaseLiveTailRightSeedReceiver
    (tag : Tag A strategy hwin) (state : TailState A strategy hwin tag)
    (row : PairedEntryRow) : RightReceiver A strategy hwin tag :=
  ⟨state,
    profiledRawJointHybridShadowPhaseLiveTailRightPayloadAtRow A strategy hwin
      tag state row⟩

noncomputable def profiledRawJointHybridShadowPhaseLiveTailLeftSeedReceiver
    (tag : Tag A strategy hwin) (state : TailState A strategy hwin tag)
    (row : PairedEntryRow) : LeftReceiver A strategy hwin tag :=
  ⟨state,
    profiledRawJointHybridShadowPhaseLiveTailLeftPayloadAtRow A strategy hwin
      tag state row⟩

/-- A present right move makes the two canonical endpoint values an exact
one-table pair. -/
theorem profiledRawJointHybridShadowPhaseLiveTailRightSeed_aligned
    (tag : Tag A strategy hwin) (state : TailState A strategy hwin tag)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (hmove : state.1.2.1 = some move) (row : PairedEntryRow) :
    ProfiledRawJointHybridShadowPhaseLiveTailRightSingleTableAligned A strategy
      hwin tag
      (profiledRawJointHybridShadowPhaseLiveTailRightSeedOwner A strategy hwin
        tag state)
      (profiledRawJointHybridShadowPhaseLiveTailRightSeedReceiver A strategy
        hwin tag state row) := by
  refine ⟨state, move,
    (profiledRawJointHybridShadowPhaseLiveTailDecoratedRightMemberController A
      strategy hwin state move false).initial,
    row,
    (profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A strategy
      hwin move false).initial,
    none, ?_, ?_⟩
  · simp [profiledRawJointHybridShadowPhaseLiveTailRightSeedOwner,
      profiledRawJointHybridShadowPhaseLiveTailRightSharedInitial, hmove]
  · simp [profiledRawJointHybridShadowPhaseLiveTailRightSeedReceiver,
      profiledRawJointHybridShadowPhaseLiveTailRightPayloadAtRow,
      profiledRawJointHybridPhysicalCompatibleRightPayloadAtRow, hmove]
    rfl

/-- Left canonical alignment. -/
theorem profiledRawJointHybridShadowPhaseLiveTailLeftSeed_aligned
    (tag : Tag A strategy hwin) (state : TailState A strategy hwin tag)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hmove : state.1.2.2 = some move) (row : PairedEntryRow) :
    ProfiledRawJointHybridShadowPhaseLiveTailLeftSingleTableAligned A strategy
      hwin tag
      (profiledRawJointHybridShadowPhaseLiveTailLeftSeedOwner A strategy hwin
        tag state)
      (profiledRawJointHybridShadowPhaseLiveTailLeftSeedReceiver A strategy
        hwin tag state row) := by
  refine ⟨state, move,
    (profiledRawJointHybridShadowPhaseLiveTailDecoratedLeftMemberController A
      strategy hwin state move false).initial,
    row,
    (profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A strategy
      hwin move false).initial,
    none, ?_, ?_⟩
  · simp [profiledRawJointHybridShadowPhaseLiveTailLeftSeedOwner,
      profiledRawJointHybridShadowPhaseLiveTailLeftSharedInitial, hmove]
  · simp [profiledRawJointHybridShadowPhaseLiveTailLeftSeedReceiver,
      profiledRawJointHybridShadowPhaseLiveTailLeftPayloadAtRow,
      profiledRawJointHybridPhysicalCompatibleLeftPayloadAtRow, hmove]
    rfl

/-! ## Exact successors reinstall an aligned pair -/

theorem
    ProfiledRawJointHybridShadowPhaseLiveTailTargetTransitionAt.rightSeed_aligned
    {tag : Tag A strategy hwin}
    {state next : TailState A strategy hwin tag}
    {root : ProfiledRawJointThreadRoot A}
    (transition :
      ProfiledRawJointHybridShadowPhaseLiveTailTargetTransitionAt A strategy
        hwin tag state next .right root)
    (row : PairedEntryRow) :
    ProfiledRawJointHybridShadowPhaseLiveTailRightSingleTableAligned A strategy
      hwin tag
      (profiledRawJointHybridShadowPhaseLiveTailRightSeedOwner A strategy hwin
        tag next)
      (profiledRawJointHybridShadowPhaseLiveTailRightSeedReceiver A strategy
        hwin tag next row) := by
  obtain ⟨move, hmove⟩ := transition.child_move
  exact profiledRawJointHybridShadowPhaseLiveTailRightSeed_aligned A strategy
    hwin tag next move hmove row

theorem
    ProfiledRawJointHybridShadowPhaseLiveTailTargetTransitionAt.leftSeed_aligned
    {tag : Tag A strategy hwin}
    {state next : TailState A strategy hwin tag}
    {root : ProfiledRawJointThreadRoot A}
    (transition :
      ProfiledRawJointHybridShadowPhaseLiveTailTargetTransitionAt A strategy
        hwin tag state next .left root)
    (row : PairedEntryRow) :
    ProfiledRawJointHybridShadowPhaseLiveTailLeftSingleTableAligned A strategy
      hwin tag
      (profiledRawJointHybridShadowPhaseLiveTailLeftSeedOwner A strategy hwin
        tag next)
      (profiledRawJointHybridShadowPhaseLiveTailLeftSeedReceiver A strategy
        hwin tag next row) := by
  obtain ⟨move, hmove⟩ := transition.child_move
  exact profiledRawJointHybridShadowPhaseLiveTailLeftSeed_aligned A strategy
    hwin tag next move hmove row

/-! ## Alignment is closed under one table calculation -/

/-- Advancing an explicit right sender and retained receiver preserves their
key/move alignment. -/
theorem profiledRawJointHybridShadowPhaseLiveTailRightSingleTableAligned_stepFor
    (tag : Tag A strategy hwin) (state : TailState A strategy hwin tag)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (ownerControl : (move.memberController A false).Control)
    (row : PairedEntryRow)
    (monitorState :
      (profiledRawJointHybridShadowPhaseLiveTailSuccessorRightMonitor A strategy
        hwin (tag := tag) move false).State)
    (staged : Option
      (ProfiledRawJointHybridShadowPhaseLiveTailRightReceiverOutput A strategy
        hwin tag))
    (member : Bool) (input : In₁ × In₂) :
    ProfiledRawJointHybridShadowPhaseLiveTailRightSingleTableAligned A strategy
      hwin tag
      ⟨state,
        (profiledRawJointHybridShadowPhaseLiveTailRightSharedStep A strategy
          hwin tag state member (.inr ⟨move, ownerControl⟩) input.1).1⟩
      (profiledRawJointHybridShadowPhaseLiveTailRightReceiverStepFor A strategy
        hwin tag state move ownerControl row monitorState
          (input.2, input.1)).2 := by
  let nextControl :=
    (profiledRawJointRightPhysicalSiblingDeferredStep A move member ownerControl
      input.1).1
  let monitor :=
    profiledRawJointHybridShadowPhaseLiveTailSuccessorRightMonitor A strategy
      hwin (tag := tag) move false
  let controller :=
    profiledRawJointHybridShadowPhaseLiveTailDecoratedRightMemberController A
      strategy hwin state move false
  let label := controller.labelOf ownerControl
  let output := label.2 monitorState (input.2, input.1)
  let nextMonitor := monitor.step monitorState
    ((input.2, input.1), output, label.1 input.1)
  refine ⟨state, move, nextControl, row, nextMonitor, some output, ?_, ?_⟩
  · simp [profiledRawJointHybridShadowPhaseLiveTailRightSharedStep,
      nextControl]
  · simp [profiledRawJointHybridShadowPhaseLiveTailRightReceiverStepFor,
      monitor, controller, label, output, nextMonitor]
    rfl

/-- Every aligned right pair exposes explicit next values satisfying the same
alignment.  Keeping the result in `Prop` avoids extracting data from an
alignment proof into executable code. -/
theorem
    ProfiledRawJointHybridShadowPhaseLiveTailRightSingleTableAligned.exists_step
    (tag : Tag A strategy hwin)
    (owner : RightOwner A strategy hwin tag)
    (receiver : RightReceiver A strategy hwin tag)
    (haligned :
      ProfiledRawJointHybridShadowPhaseLiveTailRightSingleTableAligned A
        strategy hwin tag owner receiver)
    (member : Bool) (input : In₁ × In₂) :
    ∃ (state : TailState A strategy hwin tag)
        (move : ProfiledRawJointRightPhysicalSiblingMove A)
        (ownerControl : (move.memberController A false).Control)
        (row : PairedEntryRow)
        (monitorState :
          (profiledRawJointHybridShadowPhaseLiveTailSuccessorRightMonitor A
            strategy hwin (tag := tag) move false).State)
        (staged : Option
          (ProfiledRawJointHybridShadowPhaseLiveTailRightReceiverOutput A
            strategy hwin tag)),
      owner = ⟨state, .inr ⟨move, ownerControl⟩⟩ ∧
        receiver = ⟨state, some ⟨move, row, monitorState, staged⟩⟩ ∧
        ProfiledRawJointHybridShadowPhaseLiveTailRightSingleTableAligned A
          strategy hwin tag
          ⟨state,
            (profiledRawJointHybridShadowPhaseLiveTailRightSharedStep A strategy
              hwin tag state member (.inr ⟨move, ownerControl⟩) input.1).1⟩
          (profiledRawJointHybridShadowPhaseLiveTailRightReceiverStepFor A
            strategy hwin tag state move ownerControl row monitorState
              (input.2, input.1)).2 := by
  rcases haligned with
    ⟨state, move, ownerControl, row, monitorState, staged, howner,
      hreceiver⟩
  refine ⟨state, move, ownerControl, row, monitorState, staged, howner,
    hreceiver, ?_⟩
  exact
    profiledRawJointHybridShadowPhaseLiveTailRightSingleTableAligned_stepFor A
      strategy hwin tag state move ownerControl row monitorState staged member
        input

/-- Left-table mirror. -/
theorem profiledRawJointHybridShadowPhaseLiveTailLeftSingleTableAligned_stepFor
    (tag : Tag A strategy hwin) (state : TailState A strategy hwin tag)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (ownerControl : (move.memberController A false).Control)
    (row : PairedEntryRow)
    (monitorState :
      (profiledRawJointHybridShadowPhaseLiveTailSuccessorLeftMonitor A strategy
        hwin (tag := tag) move false).State)
    (staged : Option
      (ProfiledRawJointHybridShadowPhaseLiveTailLeftReceiverOutput A strategy
        hwin tag))
    (member : Bool) (input : In₁ × In₂) :
    ProfiledRawJointHybridShadowPhaseLiveTailLeftSingleTableAligned A strategy
      hwin tag
      ⟨state,
        (profiledRawJointHybridShadowPhaseLiveTailLeftSharedStep A strategy hwin
          tag state member (.inr ⟨move, ownerControl⟩) input.2).1⟩
      (profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStepFor A strategy
        hwin tag state move ownerControl row monitorState input).2 := by
  let nextControl :=
    (profiledRawJointLeftPhysicalSiblingDeferredStep A move member ownerControl
      input.2).1
  let monitor :=
    profiledRawJointHybridShadowPhaseLiveTailSuccessorLeftMonitor A strategy
      hwin (tag := tag) move false
  let controller :=
    profiledRawJointHybridShadowPhaseLiveTailDecoratedLeftMemberController A
      strategy hwin state move false
  let label := controller.labelOf ownerControl
  let output := label.2 monitorState input
  let nextMonitor := monitor.step monitorState
    (input, output, label.1 input.2)
  refine ⟨state, move, nextControl, row, nextMonitor, some output, ?_, ?_⟩
  · simp [profiledRawJointHybridShadowPhaseLiveTailLeftSharedStep,
      nextControl]
  · simp [profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStepFor,
      monitor, controller, label, output, nextMonitor]
    rfl

theorem
    ProfiledRawJointHybridShadowPhaseLiveTailLeftSingleTableAligned.exists_step
    (tag : Tag A strategy hwin)
    (owner : LeftOwner A strategy hwin tag)
    (receiver : LeftReceiver A strategy hwin tag)
    (haligned :
      ProfiledRawJointHybridShadowPhaseLiveTailLeftSingleTableAligned A strategy
        hwin tag owner receiver)
    (member : Bool) (input : In₁ × In₂) :
    ∃ (state : TailState A strategy hwin tag)
        (move : ProfiledRawJointLeftPhysicalSiblingMove A)
        (ownerControl : (move.memberController A false).Control)
        (row : PairedEntryRow)
        (monitorState :
          (profiledRawJointHybridShadowPhaseLiveTailSuccessorLeftMonitor A
            strategy hwin (tag := tag) move false).State)
        (staged : Option
          (ProfiledRawJointHybridShadowPhaseLiveTailLeftReceiverOutput A
            strategy hwin tag)),
      owner = ⟨state, .inr ⟨move, ownerControl⟩⟩ ∧
        receiver = ⟨state, some ⟨move, row, monitorState, staged⟩⟩ ∧
        ProfiledRawJointHybridShadowPhaseLiveTailLeftSingleTableAligned A
          strategy hwin tag
          ⟨state,
            (profiledRawJointHybridShadowPhaseLiveTailLeftSharedStep A strategy
              hwin tag state member (.inr ⟨move, ownerControl⟩) input.2).1⟩
          (profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStepFor A
            strategy hwin tag state move ownerControl row monitorState input).2 := by
  rcases haligned with
    ⟨state, move, ownerControl, row, monitorState, staged, howner,
      hreceiver⟩
  refine ⟨state, move, ownerControl, row, monitorState, staged, howner,
    hreceiver, ?_⟩
  exact
    profiledRawJointHybridShadowPhaseLiveTailLeftSingleTableAligned_stepFor A
      strategy hwin tag state move ownerControl row monitorState staged member
        input

end

end DetParityAutomaton

end DistributedSynthesis
