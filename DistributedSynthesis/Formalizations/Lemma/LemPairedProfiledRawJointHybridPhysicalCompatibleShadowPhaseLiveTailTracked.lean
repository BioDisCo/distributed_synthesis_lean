/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailTableInvariant
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailLiteralPrefix

/-!
# Reachable literal live tables in one tagged recurrent tail

`TailTableInvariant` is the finite-data alignment used by the controller.
This file strengthens one selected table with the proof-only facts needed to
derive its next root-aligned successor key: tagged-tail reachability, a live
one-sided root, and one literal common owner/receiver prefix.

No prefix, root, graph direction, or leader flag is executable controller
data.
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

private abbrev TailInitial (tag : Tag A strategy hwin) :=
  (profiledRawJointHybridShadowPhaseLiveInstalled A strategy hwin
    tag.origin).world

private abbrev RightOwner (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailFrontierOneShared A strategy hwin tag

private abbrev LeftOwner (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailFrontierTwoShared A strategy hwin tag

private abbrev RightReceiver (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailRightReceiver A strategy hwin tag

private abbrev LeftReceiver (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailLeftReceiver A strategy hwin tag

private abbrev RightOutput (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailRightReceiverOutput A strategy hwin tag

private abbrev LeftOutput (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailLeftReceiverOutput A strategy hwin tag

/-! ## Target safety from one literal prefix -/

theorem profiledRawJointHybridShadowPhaseLiveTailRightReceiverStepFor_targetSafe
    (tag : Tag A strategy hwin) (state : TailState A strategy hwin tag)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (monitorState :
      (profiledRawJointHybridShadowPhaseLiveTailSuccessorRightMonitor A strategy
        hwin (tag := tag) move false).State)
    (past : List (In₂ × In₁))
    (hlocal :
      ProfiledRawJointHybridShadowPhaseLiveTailRightLocallyReachableAt A
        strategy hwin tag state move owner monitorState past)
    (row : PairedEntryRow) (input : In₂ × In₁) :
    let output :=
      (profiledRawJointHybridShadowPhaseLiveTailRightReceiverStepFor A strategy
        hwin tag state move owner row monitorState input).1
    profiledRawJointRightPhysicalSiblingAllowed A move.1
        (output.target row).1.1 ∧
      ∃ slot : ProfiledRawLeftSlot A,
        (output.target row).1.1.family.left () = some slot := by
  dsimp only
  have houtput := hlocal.output_eq_play A strategy hwin false row input
  let env : Nat → In₂ × In₁ := omegaOfList (past ++ [input])
  let play :=
    profiledRawJointHybridShadowPhaseLiveTailRightPhysicalPlay A strategy hwin
      tag state move false env
  have hsafe :=
    profiledRawJointTargetRight_targetsSafe_of_wins A
      (profiledRawJointUnitRightTargetProjection A)
      (profiledRawJointRightPhysicalSiblingAllowed A move.1)
      move.1.source play
      (profiledRawJointHybridShadowPhaseLiveTailRightPhysicalPlay_wins A
        strategy hwin tag state move false env)
      past.length row
  have hprojection :
      profiledRawJointHybridShadowPhaseLiveTailRightReceiverProjection A
          strategy hwin
          (profiledRawJointHybridShadowPhaseLiveTailRightReceiverStepFor A
            strategy hwin tag state move owner row monitorState input).1 =
        (play past.length).2.1 := by
    rw [houtput]
    rfl
  have htarget :
      ((profiledRawJointHybridShadowPhaseLiveTailRightReceiverStepFor A strategy
        hwin tag state move owner row monitorState input).1.target row).1.1 =
        (play past.length).2.1.target row := by
    exact congrArg (fun output ↦ output.target row) hprojection
  rw [htarget]
  refine ⟨hsafe.2, ?_⟩
  exact exists_profiledRawJointLeftSlot_of_rightPhysicalTargetSafe A
    ((play past.length).2.1.target row)
    (((profiledRawJointRightPhysicalSiblingMonitor A move.1 false).run play
      past.length).2.1)
    row (profiledRawJointTargetRightPhysicalLetter A (play past.length))
    hsafe.1

theorem profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStepFor_targetSafe
    (tag : Tag A strategy hwin) (state : TailState A strategy hwin tag)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (monitorState :
      (profiledRawJointHybridShadowPhaseLiveTailSuccessorLeftMonitor A strategy
        hwin (tag := tag) move false).State)
    (past : List (In₁ × In₂))
    (hlocal :
      ProfiledRawJointHybridShadowPhaseLiveTailLeftLocallyReachableAt A strategy
        hwin tag state move owner monitorState past)
    (row : PairedEntryRow) (input : In₁ × In₂) :
    let output :=
      (profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStepFor A strategy
        hwin tag state move owner row monitorState input).1
    profiledRawJointLeftPhysicalSiblingAllowed A move.1
        (output.target row).1.1 ∧
      ∃ slot : ProfiledRawRightSlot A,
        (output.target row).1.1.family.right () = some slot := by
  dsimp only
  have houtput := hlocal.output_eq_play A strategy hwin false row input
  let env : Nat → In₁ × In₂ := omegaOfList (past ++ [input])
  let play :=
    profiledRawJointHybridShadowPhaseLiveTailLeftPhysicalPlay A strategy hwin
      tag state move false env
  have hsafe :=
    profiledRawJointTargetLeft_targetsSafe_of_wins A
      (profiledRawJointUnitLeftTargetProjection A)
      (profiledRawJointLeftPhysicalSiblingAllowed A move.1)
      move.1.source play
      (profiledRawJointHybridShadowPhaseLiveTailLeftPhysicalPlay_wins A strategy
        hwin tag state move false env)
      past.length row
  have hprojection :
      profiledRawJointHybridShadowPhaseLiveTailLeftReceiverProjection A strategy
          hwin
          (profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStepFor A
            strategy hwin tag state move owner row monitorState input).1 =
        (play past.length).2.1 := by
    rw [houtput]
    rfl
  have htarget :
      ((profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStepFor A strategy
        hwin tag state move owner row monitorState input).1.target row).1.1 =
        (play past.length).2.1.target row := by
    exact congrArg (fun output ↦ output.target row) hprojection
  rw [htarget]
  refine ⟨hsafe.2, ?_⟩
  exact exists_profiledRawJointRightSlot_of_leftPhysicalTargetSafe A
    ((play past.length).2.1.target row)
    (((profiledRawJointLeftPhysicalSiblingMonitor A move.1 false).run play
      past.length).2.1)
    row (profiledRawJointTargetLeftPhysicalLetter A (play past.length)) hsafe.1

/-! ## Strong selected-table relations -/

def ProfiledRawJointHybridShadowPhaseLiveTailRightTracked
    (tag : Tag A strategy hwin) (owner : RightOwner A strategy hwin tag)
    (receiver : RightReceiver A strategy hwin tag) : Prop :=
  ∃ (state : TailState A strategy hwin tag)
      (move : ProfiledRawJointRightPhysicalSiblingMove A)
      (ownerControl : (move.memberController A false).Control)
      (row : PairedEntryRow)
      (monitorState :
        (profiledRawJointHybridShadowPhaseLiveTailSuccessorRightMonitor A
          strategy hwin (tag := tag) move false).State)
      (staged : Option (RightOutput A strategy hwin tag))
      (past : List (In₂ × In₁)),
    owner = ⟨state, .inr ⟨move, ownerControl⟩⟩ ∧
      receiver = ⟨state, some ⟨move, row, monitorState, staged⟩⟩ ∧
      state.1.2.1 = some move ∧
      tag.TailReachable A strategy hwin state ∧
      (∃ code : ProfiledRawJointIncidenceCode A (I := Unit),
        state.1.1 = .oneSided code) ∧
      (∃ root : ProfiledRawJointThreadRoot A,
        profiledRawJointHybridCurrentSlots A .right state.1.1 () = some root) ∧
      ProfiledRawJointHybridShadowPhaseLiveTailRightLocallyReachableAt A
        strategy hwin tag state move ownerControl monitorState past

def ProfiledRawJointHybridShadowPhaseLiveTailLeftTracked
    (tag : Tag A strategy hwin) (owner : LeftOwner A strategy hwin tag)
    (receiver : LeftReceiver A strategy hwin tag) : Prop :=
  ∃ (state : TailState A strategy hwin tag)
      (move : ProfiledRawJointLeftPhysicalSiblingMove A)
      (ownerControl : (move.memberController A false).Control)
      (row : PairedEntryRow)
      (monitorState :
        (profiledRawJointHybridShadowPhaseLiveTailSuccessorLeftMonitor A strategy
          hwin (tag := tag) move false).State)
      (staged : Option (LeftOutput A strategy hwin tag))
      (past : List (In₁ × In₂)),
    owner = ⟨state, .inr ⟨move, ownerControl⟩⟩ ∧
      receiver = ⟨state, some ⟨move, row, monitorState, staged⟩⟩ ∧
      state.1.2.2 = some move ∧
      tag.TailReachable A strategy hwin state ∧
      (∃ code : ProfiledRawJointIncidenceCode A (I := Unit),
        state.1.1 = .oneSided code) ∧
      (∃ root : ProfiledRawJointThreadRoot A,
        profiledRawJointHybridCurrentSlots A .left state.1.1 () = some root) ∧
      ProfiledRawJointHybridShadowPhaseLiveTailLeftLocallyReachableAt A strategy
        hwin tag state move ownerControl monitorState past

theorem ProfiledRawJointHybridShadowPhaseLiveTailRightTracked.aligned
    {tag : Tag A strategy hwin} {owner : RightOwner A strategy hwin tag}
    {receiver : RightReceiver A strategy hwin tag}
    (tracked : ProfiledRawJointHybridShadowPhaseLiveTailRightTracked A strategy
      hwin tag owner receiver) :
    ProfiledRawJointHybridShadowPhaseLiveTailRightSingleTableAligned A strategy
      hwin tag owner receiver := by
  rcases tracked with
    ⟨state, move, ownerControl, row, monitorState, staged, past, howner,
      hreceiver, _⟩
  exact ⟨state, move, ownerControl, row, monitorState, staged, howner,
    hreceiver⟩

theorem ProfiledRawJointHybridShadowPhaseLiveTailLeftTracked.aligned
    {tag : Tag A strategy hwin} {owner : LeftOwner A strategy hwin tag}
    {receiver : LeftReceiver A strategy hwin tag}
    (tracked : ProfiledRawJointHybridShadowPhaseLiveTailLeftTracked A strategy
      hwin tag owner receiver) :
    ProfiledRawJointHybridShadowPhaseLiveTailLeftSingleTableAligned A strategy
      hwin tag owner receiver := by
  rcases tracked with
    ⟨state, move, ownerControl, row, monitorState, staged, past, howner,
      hreceiver, _⟩
  exact ⟨state, move, ownerControl, row, monitorState, staged, howner,
    hreceiver⟩

theorem ProfiledRawJointHybridShadowPhaseLiveTailRightTracked.owner_reachable
    {tag : Tag A strategy hwin} {owner : RightOwner A strategy hwin tag}
    {receiver : RightReceiver A strategy hwin tag}
    (tracked : ProfiledRawJointHybridShadowPhaseLiveTailRightTracked A strategy
      hwin tag owner receiver) :
    tag.TailReachable A strategy hwin owner.1 := by
  rcases tracked with
    ⟨state, move, ownerControl, row, monitorState, staged, past, rfl, _, _,
      hreachable, _⟩
  exact hreachable

theorem ProfiledRawJointHybridShadowPhaseLiveTailLeftTracked.owner_reachable
    {tag : Tag A strategy hwin} {owner : LeftOwner A strategy hwin tag}
    {receiver : LeftReceiver A strategy hwin tag}
    (tracked : ProfiledRawJointHybridShadowPhaseLiveTailLeftTracked A strategy
      hwin tag owner receiver) :
    tag.TailReachable A strategy hwin owner.1 := by
  rcases tracked with
    ⟨state, move, ownerControl, row, monitorState, staged, past, rfl, _, _,
      hreachable, _⟩
  exact hreachable

/-! ## A tracked selected step emits its root-aligned successor key -/

theorem
    ProfiledRawJointHybridShadowPhaseLiveTailRightTracked.key
    {tag : Tag A strategy hwin} {owner : RightOwner A strategy hwin tag}
    {receiver : RightReceiver A strategy hwin tag}
    (tracked : ProfiledRawJointHybridShadowPhaseLiveTailRightTracked A strategy
      hwin tag owner receiver)
    (fallback : RightOutput A strategy hwin tag) (input : In₂ × In₁) :
    let row :=
      profiledRawJointHybridShadowPhaseLiveTailRightReceiverRow A strategy hwin
        tag receiver
    let output :=
      (profiledRawJointHybridShadowPhaseLiveTailRightReceiverStep A strategy
        hwin tag fallback owner receiver input).1
    ProfiledRawJointHybridShadowPhaseLiveTailRightSuccessorKeyAt A strategy hwin
      owner.1
        (profiledRawJointHybridShadowPhaseLiveTailSuccessorTargetKey A strategy
          hwin (output.target row).1)
        (output.target row).1.1 := by
  rcases tracked with
    ⟨state, move, ownerControl, row, monitorState, staged, past, rfl, rfl,
      hmove, hreachable, ⟨code, hcode⟩, ⟨root, hlive⟩, hlocal⟩
  simp only [profiledRawJointHybridShadowPhaseLiveTailRightReceiverRow,
    profiledRawJointHybridShadowPhaseLiveTailRightReceiverStep_live]
  let output :=
    (profiledRawJointHybridShadowPhaseLiveTailRightReceiverStepFor A strategy
      hwin tag state move ownerControl row monitorState input).1
  let raw :=
    profiledRawJointHybridShadowPhaseLiveTailRightReceiverProjection A strategy
      hwin output
  have hsafe :=
    profiledRawJointHybridShadowPhaseLiveTailRightReceiverStepFor_targetSafe A
      strategy hwin tag state move ownerControl monitorState past hlocal row
        input
  obtain ⟨slot, hslot⟩ := hsafe.2
  have hdecorated :
      profiledRawJointHybridShadowPhaseLiveTailDecorateRightReceiverOutput A
          strategy hwin state raw = output := by
    rfl
  have hkey :=
    profiledRawJointHybridShadowPhaseLiveTailDecorateRightReceiverOutput_key A
      strategy hwin state hreachable code hcode root hlive move hmove raw row
        hsafe.1 slot hslot
  rw [hdecorated] at hkey
  exact hkey

theorem
    ProfiledRawJointHybridShadowPhaseLiveTailLeftTracked.key
    {tag : Tag A strategy hwin} {owner : LeftOwner A strategy hwin tag}
    {receiver : LeftReceiver A strategy hwin tag}
    (tracked : ProfiledRawJointHybridShadowPhaseLiveTailLeftTracked A strategy
      hwin tag owner receiver)
    (fallback : LeftOutput A strategy hwin tag) (input : In₁ × In₂) :
    let row :=
      profiledRawJointHybridShadowPhaseLiveTailLeftReceiverRow A strategy hwin
        tag receiver
    let output :=
      (profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStep A strategy hwin
        tag fallback owner receiver input).1
    ProfiledRawJointHybridShadowPhaseLiveTailLeftSuccessorKeyAt A strategy hwin
      owner.1
        (profiledRawJointHybridShadowPhaseLiveTailSuccessorTargetKey A strategy
          hwin (output.target row).1)
        (output.target row).1.1 := by
  rcases tracked with
    ⟨state, move, ownerControl, row, monitorState, staged, past, rfl, rfl,
      hmove, hreachable, ⟨code, hcode⟩, ⟨root, hlive⟩, hlocal⟩
  simp only [profiledRawJointHybridShadowPhaseLiveTailLeftReceiverRow,
    profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStep_live]
  let output :=
    (profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStepFor A strategy hwin
      tag state move ownerControl row monitorState input).1
  let raw :=
    profiledRawJointHybridShadowPhaseLiveTailLeftReceiverProjection A strategy
      hwin output
  have hsafe :=
    profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStepFor_targetSafe A
      strategy hwin tag state move ownerControl monitorState past hlocal row
        input
  obtain ⟨slot, hslot⟩ := hsafe.2
  have hdecorated :
      profiledRawJointHybridShadowPhaseLiveTailDecorateLeftReceiverOutput A
          strategy hwin state raw = output := by
    rfl
  have hkey :=
    profiledRawJointHybridShadowPhaseLiveTailDecorateLeftReceiverOutput_key A
      strategy hwin state hreachable code hcode root hlive move hmove raw row
        hsafe.1 slot hslot
  rw [hdecorated] at hkey
  exact hkey

/-! ## Repeated one-way rounds preserve the tracked table -/

theorem ProfiledRawJointHybridShadowPhaseLiveTailRightTracked.step
    {tag : Tag A strategy hwin} {owner : RightOwner A strategy hwin tag}
    {receiver : RightReceiver A strategy hwin tag}
    (tracked : ProfiledRawJointHybridShadowPhaseLiveTailRightTracked A strategy
      hwin tag owner receiver)
    (fallback : RightOutput A strategy hwin tag) (member : Bool)
    (input : In₂ × In₁) :
    ProfiledRawJointHybridShadowPhaseLiveTailRightTracked A strategy hwin tag
      ⟨owner.1,
        (profiledRawJointHybridShadowPhaseLiveTailRightSharedStep A strategy
          hwin tag owner.1 member owner.2 input.2).1⟩
      (profiledRawJointHybridShadowPhaseLiveTailRightReceiverStep A strategy hwin
        tag fallback owner receiver input).2 := by
  rcases tracked with
    ⟨state, move, ownerControl, row, monitorState, staged, past, rfl, rfl,
      hmove, hreachable, hone, hlive, hlocal⟩
  let nextControl := (move.memberController A false).step ownerControl input.2
  let monitor :=
    profiledRawJointHybridShadowPhaseLiveTailSuccessorRightMonitor A strategy
      hwin (tag := tag) move false
  let controller :=
    profiledRawJointHybridShadowPhaseLiveTailDecoratedRightMemberController A
      strategy hwin state move false
  let label := controller.labelOf ownerControl
  let output := label.2 monitorState input
  let nextMonitor := monitor.step monitorState (input, output, label.1 input.2)
  refine ⟨state, move, nextControl, row, nextMonitor, some output,
    past ++ [input], ?_, ?_, hmove, hreachable, hone, hlive, ?_⟩
  · simp [profiledRawJointHybridShadowPhaseLiveTailRightSharedStep,
      nextControl]
    exact
      (profiledRawJointRightPhysicalSiblingDeferredStep_laws A move).state_eq
        member false ownerControl input.2
  · simp [profiledRawJointHybridShadowPhaseLiveTailRightReceiverStep,
      profiledRawJointHybridShadowPhaseLiveTailRightReceiverStepFor,
      monitor, controller, label, output, nextMonitor]
    rfl
  · simpa [nextControl, nextMonitor, monitor, controller, label, output,
      profiledRawJointHybridShadowPhaseLiveTailRightReceiverStepFor] using
      (hlocal.step A strategy hwin row input)

theorem ProfiledRawJointHybridShadowPhaseLiveTailLeftTracked.step
    {tag : Tag A strategy hwin} {owner : LeftOwner A strategy hwin tag}
    {receiver : LeftReceiver A strategy hwin tag}
    (tracked : ProfiledRawJointHybridShadowPhaseLiveTailLeftTracked A strategy
      hwin tag owner receiver)
    (fallback : LeftOutput A strategy hwin tag) (member : Bool)
    (input : In₁ × In₂) :
    ProfiledRawJointHybridShadowPhaseLiveTailLeftTracked A strategy hwin tag
      ⟨owner.1,
        (profiledRawJointHybridShadowPhaseLiveTailLeftSharedStep A strategy hwin
          tag owner.1 member owner.2 input.2).1⟩
      (profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStep A strategy hwin
        tag fallback owner receiver input).2 := by
  rcases tracked with
    ⟨state, move, ownerControl, row, monitorState, staged, past, rfl, rfl,
      hmove, hreachable, hone, hlive, hlocal⟩
  let nextControl := (move.memberController A false).step ownerControl input.2
  let monitor :=
    profiledRawJointHybridShadowPhaseLiveTailSuccessorLeftMonitor A strategy hwin
      (tag := tag) move false
  let controller :=
    profiledRawJointHybridShadowPhaseLiveTailDecoratedLeftMemberController A
      strategy hwin state move false
  let label := controller.labelOf ownerControl
  let output := label.2 monitorState input
  let nextMonitor := monitor.step monitorState (input, output, label.1 input.2)
  refine ⟨state, move, nextControl, row, nextMonitor, some output,
    past ++ [input], ?_, ?_, hmove, hreachable, hone, hlive, ?_⟩
  · simp [profiledRawJointHybridShadowPhaseLiveTailLeftSharedStep,
      nextControl]
    exact
      (profiledRawJointLeftPhysicalSiblingDeferredStep_laws A move).state_eq
        member false ownerControl input.2
  · simp [profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStep,
      profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStepFor,
      monitor, controller, label, output, nextMonitor]
    rfl
  · simpa [nextControl, nextMonitor, monitor, controller, label, output,
      profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStepFor] using
      (hlocal.step A strategy hwin row input)

/-! ## Exact successor keys initialize fresh tracked tables -/

theorem profiledRawJointHybridShadowPhaseLiveTailFreshRight_tracked_of_key
    (tag : Tag A strategy hwin) (state : TailState A strategy hwin tag)
    (hstate : tag.TailReachable A strategy hwin state)
    (parent : RightOwner A strategy hwin tag)
    (output : LeftOutput A strategy hwin tag) (entryRow : PairedEntryRow)
    (receiverMember : Bool)
    (hkey :
      ProfiledRawJointHybridShadowPhaseLiveTailLeftSuccessorKeyAt A strategy
        hwin state
          (profiledRawJointHybridShadowPhaseLiveTailSuccessorTargetKey A
            strategy hwin (output.target entryRow).1)
          (output.target entryRow).1.1) :
    let payload :=
      profiledRawJointHybridShadowPhaseLiveTailLeftPendingPayloadOfOutput A
        strategy hwin tag output entryRow
    ProfiledRawJointHybridShadowPhaseLiveTailRightTracked A strategy hwin tag
      (profiledRawJointHybridShadowPhaseLiveTailFreshRightOwner A strategy hwin
        tag parent payload)
      (profiledRawJointHybridShadowPhaseLiveTailFreshRightReceiver A strategy
        hwin tag payload receiverMember) := by
  dsimp only
  rcases hkey with ⟨slot, hlive, ⟨aligned⟩⟩
  obtain ⟨move, hmove⟩ := aligned.transition.child_move
  change
    (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy hwin
      (output.target entryRow).1).1.2.1 = some move at hmove
  unfold profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey at hmove
  obtain ⟨code, hcode⟩ := aligned.transition.child_oneSided
  have hreachable := aligned.reachable A strategy hwin hstate
  let next :=
    profiledRawJointHybridShadowPhaseLiveTailSuccessorTargetKey A strategy hwin
      (output.target entryRow).1
  let ownerControl :=
    (profiledRawJointHybridShadowPhaseLiveTailDecoratedRightMemberController A
      strategy hwin next move false).initial
  let monitorState :=
    (profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A strategy
      hwin (initial := TailInitial A strategy hwin tag) move false).initial
  let row :=
    profiledRawJointHybridPhysicalCompatiblePendingRow receiverMember
  have htargetFalse :=
    profiledRawJointHybridShadowPhaseLiveTailLeftPendingPayloadOfOutput_target A
      strategy hwin tag output entryRow false
  have htargetMember :=
    profiledRawJointHybridShadowPhaseLiveTailLeftPendingPayloadOfOutput_target A
      strategy hwin tag output entryRow receiverMember
  refine ⟨next, move, ownerControl, row, monitorState, none, [], ?_, ?_,
    hmove, hreachable, ⟨code, hcode⟩, ⟨.inl slot,
      aligned.transition.child_live⟩, ?_⟩
  · simp only [profiledRawJointHybridShadowPhaseLiveTailFreshRightOwner]
    rw [htargetFalse]
    simp [next, ownerControl,
      profiledRawJointHybridShadowPhaseLiveTailSuccessorTargetKey,
      profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey,
      profiledRawJointHybridShadowPhaseLiveTailRightSharedInitial, hmove]
  · simp only [profiledRawJointHybridShadowPhaseLiveTailFreshRightReceiver]
    rw [htargetMember]
    simp [next, row, monitorState,
      profiledRawJointHybridShadowPhaseLiveTailLeftPendingPayloadOfOutput,
      profiledRawJointHybridShadowPhaseLiveTailLeftPendingPayloadReceiver,
      profiledRawJointHybridShadowPhaseLiveTailSuccessorTargetKey,
      profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey,
      profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadOfOutput_receiver,
      profiledRawJointHybridPhysicalCompatibleRightPayloadAtRow, hmove]
    rfl
  · simpa [ownerControl, monitorState] using
      (profiledRawJointHybridShadowPhaseLiveTailRightLocallyReachableAt_initial A
        strategy hwin tag next move)

theorem profiledRawJointHybridShadowPhaseLiveTailFreshLeft_tracked_of_key
    (tag : Tag A strategy hwin) (state : TailState A strategy hwin tag)
    (hstate : tag.TailReachable A strategy hwin state)
    (parent : LeftOwner A strategy hwin tag)
    (output : RightOutput A strategy hwin tag) (entryRow : PairedEntryRow)
    (receiverMember : Bool)
    (hkey :
      ProfiledRawJointHybridShadowPhaseLiveTailRightSuccessorKeyAt A strategy
        hwin state
          (profiledRawJointHybridShadowPhaseLiveTailSuccessorTargetKey A
            strategy hwin (output.target entryRow).1)
          (output.target entryRow).1.1) :
    let payload :=
      profiledRawJointHybridShadowPhaseLiveTailRightPendingPayloadOfOutput A
        strategy hwin tag output entryRow
    ProfiledRawJointHybridShadowPhaseLiveTailLeftTracked A strategy hwin tag
      (profiledRawJointHybridShadowPhaseLiveTailFreshLeftOwner A strategy hwin
        tag parent payload)
      (profiledRawJointHybridShadowPhaseLiveTailFreshLeftReceiver A strategy
        hwin tag payload receiverMember) := by
  dsimp only
  rcases hkey with ⟨slot, hlive, ⟨aligned⟩⟩
  obtain ⟨move, hmove⟩ := aligned.transition.child_move
  change
    (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy hwin
      (output.target entryRow).1).1.2.2 = some move at hmove
  unfold profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey at hmove
  obtain ⟨code, hcode⟩ := aligned.transition.child_oneSided
  have hreachable := aligned.reachable A strategy hwin hstate
  let next :=
    profiledRawJointHybridShadowPhaseLiveTailSuccessorTargetKey A strategy hwin
      (output.target entryRow).1
  let ownerControl :=
    (profiledRawJointHybridShadowPhaseLiveTailDecoratedLeftMemberController A
      strategy hwin next move false).initial
  let monitorState :=
    (profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A strategy
      hwin (initial := TailInitial A strategy hwin tag) move false).initial
  let row :=
    profiledRawJointHybridPhysicalCompatiblePendingRow receiverMember
  have htargetFalse :=
    profiledRawJointHybridShadowPhaseLiveTailRightPendingPayloadOfOutput_target A
      strategy hwin tag output entryRow false
  have htargetMember :=
    profiledRawJointHybridShadowPhaseLiveTailRightPendingPayloadOfOutput_target A
      strategy hwin tag output entryRow receiverMember
  refine ⟨next, move, ownerControl, row, monitorState, none, [], ?_, ?_,
    hmove, hreachable, ⟨code, hcode⟩, ⟨.inr slot,
      aligned.transition.child_live⟩, ?_⟩
  · simp only [profiledRawJointHybridShadowPhaseLiveTailFreshLeftOwner]
    rw [htargetFalse]
    simp [next, ownerControl,
      profiledRawJointHybridShadowPhaseLiveTailSuccessorTargetKey,
      profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey,
      profiledRawJointHybridShadowPhaseLiveTailLeftSharedInitial, hmove]
  · simp only [profiledRawJointHybridShadowPhaseLiveTailFreshLeftReceiver]
    rw [htargetMember]
    simp [next, row, monitorState,
      profiledRawJointHybridShadowPhaseLiveTailRightPendingPayloadOfOutput,
      profiledRawJointHybridShadowPhaseLiveTailRightPendingPayloadReceiver,
      profiledRawJointHybridShadowPhaseLiveTailSuccessorTargetKey,
      profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey,
      profiledRawJointHybridPhysicalCompatibleRightPendingPayloadOfOutput_receiver,
      profiledRawJointHybridPhysicalCompatibleLeftPayloadAtRow, hmove]
    rfl
  · simpa [ownerControl, monitorState] using
      (profiledRawJointHybridShadowPhaseLiveTailLeftLocallyReachableAt_initial A
        strategy hwin tag next move)

end

end DetParityAutomaton

end DistributedSynthesis
