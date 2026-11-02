/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleLiteralPrefixTargetRowBridge
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailTrackedRowCoupledInvariant

/-!
# Closing the row-aware Tail constructor equations

The strict switch equations are the finite target-row handoff: the retained
table realizes its emitted target profile, while the crossed fresh table is
rooted at that same finite slot and uses row `.first`.  All direction cases
are proof-side cases; neither endpoint transition receives a graph, leader,
or hierarchy bit.
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

private abbrev OnePending (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailOnePending A strategy hwin tag

private abbrev TwoPending (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailTwoPending A strategy hwin tag

private abbrev RightOutput (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailRightReceiverOutput A strategy hwin
    tag

private abbrev LeftOutput (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailLeftReceiverOutput A strategy hwin
    tag

/-! ## Prefix-parametric local readback -/

/-- The local right receiver calculation may be read in any environment with
the same old prefix and current input. -/
theorem
    ProfiledRawJointHybridShadowPhaseLiveTailRightLocallyReachableAt.output_eq_play_of_prefix
    {tag : Tag A strategy hwin}
    {state : ProfiledRawJointHybridShadowPhaseLiveTailState A strategy hwin tag}
    {move : ProfiledRawJointRightPhysicalSiblingMove A}
    {owner : (move.memberController A false).Control}
    {monitorState :
      (profiledRawJointHybridShadowPhaseLiveTailSuccessorRightMonitor A
        strategy hwin (tag := tag) move false).State}
    {past : List (In₂ × In₁)}
    (hreach :
      ProfiledRawJointHybridShadowPhaseLiveTailRightLocallyReachableAt A
        strategy hwin tag state move owner monitorState past)
    (row : PairedEntryRow) (input : In₂ × In₁)
    (env : Nat → In₂ × In₁)
    (hpast : omegaPrefix env past.length = past)
    (hinput : env past.length = input) :
    (profiledRawJointHybridShadowPhaseLiveTailRightReceiverStepFor A strategy
        hwin tag state move owner row monitorState input).1 =
      (profiledRawJointHybridShadowPhaseLiveTailRightDecoratedPlay A strategy
        hwin tag state move false env past.length).2.1 := by
  rcases hreach with ⟨howner, hmonitor⟩
  subst owner
  subst monitorState
  simp [profiledRawJointHybridShadowPhaseLiveTailRightDecoratedPlay,
    profiledRawJointHybridShadowPhaseLiveTailRightReceiverStepFor,
    treePlay, narrowedInducedTree, blockLabelApply,
    TransitionRationalTree.labeledTree, branchNode_eq_omegaPrefix,
    hpast, hinput]

/-- Left mirror of prefix-parametric local readback. -/
theorem
    ProfiledRawJointHybridShadowPhaseLiveTailLeftLocallyReachableAt.output_eq_play_of_prefix
    {tag : Tag A strategy hwin}
    {state : ProfiledRawJointHybridShadowPhaseLiveTailState A strategy hwin tag}
    {move : ProfiledRawJointLeftPhysicalSiblingMove A}
    {owner : (move.memberController A false).Control}
    {monitorState :
      (profiledRawJointHybridShadowPhaseLiveTailSuccessorLeftMonitor A strategy
        hwin (tag := tag) move false).State}
    {past : List (In₁ × In₂)}
    (hreach :
      ProfiledRawJointHybridShadowPhaseLiveTailLeftLocallyReachableAt A strategy
        hwin tag state move owner monitorState past)
    (row : PairedEntryRow) (input : In₁ × In₂)
    (env : Nat → In₁ × In₂)
    (hpast : omegaPrefix env past.length = past)
    (hinput : env past.length = input) :
    (profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStepFor A strategy
        hwin tag state move owner row monitorState input).1 =
      (profiledRawJointHybridShadowPhaseLiveTailLeftDecoratedPlay A strategy
        hwin tag state move false env past.length).2.1 := by
  rcases hreach with ⟨howner, hmonitor⟩
  subst owner
  subst monitorState
  simp [profiledRawJointHybridShadowPhaseLiveTailLeftDecoratedPlay,
    profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStepFor,
    treePlay, narrowedInducedTree, blockLabelApply,
    TransitionRationalTree.labeledTree, branchNode_eq_omegaPrefix,
    hpast, hinput]

/-! ## One retained table realizes its finite target -/

/-- After one right-table step, the following right record realizes every
live left profile emitted by the first step. -/
theorem ProfiledRawJointHybridShadowPhaseLiveTailRightTracked.nextClosing_eq_liveTarget
    {tag : Tag A strategy hwin}
    {owner : ProfiledRawJointHybridShadowPhaseLiveTailFrontierOneShared A
      strategy hwin tag}
    {receiver : ProfiledRawJointHybridShadowPhaseLiveTailRightReceiver A
      strategy hwin tag}
    (tracked : ProfiledRawJointHybridShadowPhaseLiveTailRightTracked A strategy
      hwin tag owner receiver)
    (fallback : RightOutput A strategy hwin tag) (member : Bool)
    (input nextInput : In₂ × In₁) (slot : ProfiledRawLeftSlot A)
    (hlive :
      let row :=
        profiledRawJointHybridShadowPhaseLiveTailRightReceiverRow A strategy
          hwin tag receiver
      let output :=
        (profiledRawJointHybridShadowPhaseLiveTailRightReceiverStep A strategy
          hwin tag fallback owner receiver input).1
      (output.target row).1.1.family.left () = some slot) :
    let row :=
      profiledRawJointHybridShadowPhaseLiveTailRightReceiverRow A strategy hwin
        tag receiver
    let result :=
      profiledRawJointHybridShadowPhaseLiveTailRightReceiverStep A strategy hwin
        tag fallback owner receiver input
    let nextOwner :
        ProfiledRawJointHybridShadowPhaseLiveTailFrontierOneShared A strategy
          hwin tag :=
      ⟨owner.1,
        (profiledRawJointHybridShadowPhaseLiveTailRightSharedStep A strategy
          hwin tag owner.1 member owner.2 input.2).1⟩
    pairedRightClosingForRow row
        (profiledRawJointHybridShadowPhaseLiveTailRightSingleTableRecord A
          strategy hwin tag fallback nextOwner result.2 nextInput).physical =
      slot.2 (nextInput.2, nextInput.1) := by
  rcases tracked with
    ⟨state, move, ownerControl, row, monitorState, staged, past, rfl, rfl,
      _hmove, _hreachable, _hone, _hroot, hlocal⟩
  simp only [profiledRawJointHybridShadowPhaseLiveTailRightReceiverRow,
    profiledRawJointHybridShadowPhaseLiveTailRightReceiverStep_live] at hlive ⊢
  let env : Nat → In₂ × In₁ := omegaOfList (past ++ [input, nextInput])
  have hpast : omegaPrefix env past.length = past := by
    apply List.ext_get
    · simp [env, omegaPrefix]
    · intro n hnLeft hnRight
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [omegaPrefix, List.getElem_ofFn]
      have hnPrefix : n < (past ++ [input, nextInput]).length := by
        simp
        omega
      change omegaOfList (past ++ [input, nextInput]) n = past[n]
      rw [omegaOfList_eq_getElem _ n hnPrefix]
      simp [hnRight]
  have hinput : env past.length = input := by
    simp [env, omegaOfList_eq_getElem]
  have hprefixNext :
      omegaPrefix env (past ++ [input]).length = past ++ [input] := by
    apply List.ext_get
    · simp [env, omegaPrefix]
    · intro n hnLeft hnRight
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [omegaPrefix, List.getElem_ofFn]
      have hnPrefix : n < (past ++ [input, nextInput]).length := by
        simp at hnRight ⊢
        omega
      change omegaOfList (past ++ [input, nextInput]) n =
        (past ++ [input])[n]
      rw [omegaOfList_eq_getElem _ n hnPrefix]
      have hnAppend : n < ((past ++ [input]) ++ [nextInput]).length := by
        simpa [List.append_assoc] using hnPrefix
      simpa [List.append_assoc] using
        (List.getElem_append_left (bs := [nextInput]) hnRight
          (h' := hnAppend))
  have hnextInput : env (past ++ [input]).length = nextInput := by
    simp [env, omegaOfList_eq_getElem]
  have hcurrent := hlocal.output_eq_play_of_prefix A strategy hwin row input env
    hpast hinput
  have hlocalNext := hlocal.step A strategy hwin row input
  have hnext := hlocalNext.output_eq_play_of_prefix A strategy hwin row nextInput
    env hprefixNext hnextInput
  let physicalPlay :=
    profiledRawJointHybridShadowPhaseLiveTailRightPhysicalPlay A strategy hwin
      tag state move false env
  have hcurrentPhysical :
      profiledRawJointHybridShadowPhaseLiveTailRightReceiverProjection A
          strategy hwin
          (profiledRawJointHybridShadowPhaseLiveTailRightReceiverStepFor A
            strategy hwin tag state move ownerControl row monitorState input).1 =
        (physicalPlay past.length).2.1 := by
    simpa [physicalPlay,
      profiledRawJointHybridShadowPhaseLiveTailRightPhysicalPlay] using
      congrArg
        (profiledRawJointHybridShadowPhaseLiveTailRightReceiverProjection A
          strategy hwin) hcurrent
  have hlivePhysical :
      ((physicalPlay past.length).2.1.target row).family.left () = some slot := by
    rw [← hcurrentPhysical]
    exact hlive
  have hdelay :=
    profiledRawJointRightPhysicalSiblingWinningPlay_delayedLiveSlot A move.1
      physicalPlay
      (profiledRawJointHybridShadowPhaseLiveTailRightPhysicalPlay_wins A
        strategy hwin tag state move false env)
      past.length row slot hlivePhysical
  have hnextPhysical :
      profiledRawJointHybridShadowPhaseLiveTailRightReceiverProjection A
          strategy hwin
          (profiledRawJointHybridShadowPhaseLiveTailRightReceiverStepFor A
            strategy hwin tag state move
              ((move.memberController A false).step ownerControl input.2) row
              ((profiledRawJointHybridShadowPhaseLiveTailRightReceiverStepFor A
                strategy hwin tag state move ownerControl row monitorState
                  input).2.2.get (by rfl)).2.2.1 nextInput).1 =
        (physicalPlay (past.length + 1)).2.1 := by
    simpa [physicalPlay,
      profiledRawJointHybridShadowPhaseLiveTailRightPhysicalPlay] using
      congrArg
        (profiledRawJointHybridShadowPhaseLiveTailRightReceiverProjection A
          strategy hwin) hnext
  rw [← hnextPhysical] at hdelay
  have hownerAdvance :=
    (profiledRawJointRightPhysicalSiblingDeferredStep_laws A move).state_eq
      member false ownerControl input.2
  simp only [profiledRawJointRightPhysicalSiblingDeferredStep] at hownerAdvance
  have hphysicalInput : (physicalPlay (past.length + 1)).1 = nextInput := by
    change env (past.length + 1) = nextInput
    simpa using hnextInput
  rw [hphysicalInput] at hdelay
  simp only [profiledRawJointHybridShadowPhaseLiveTailRightSharedStep,
    profiledRawJointRightPhysicalSiblingDeferredStep]
  rw [hownerAdvance]
  simpa [profiledRawJointHybridShadowPhaseLiveTailRightReceiverStepFor,
    profiledRawJointHybridShadowPhaseLiveTailRightReceiverProjection,
    profiledRawJointHybridShadowPhaseLiveTailRightSingleTableRecord]
    using hdelay

/-- Left-table mirror of retained target realization. -/
theorem ProfiledRawJointHybridShadowPhaseLiveTailLeftTracked.nextClosing_eq_liveTarget
    {tag : Tag A strategy hwin}
    {owner : ProfiledRawJointHybridShadowPhaseLiveTailFrontierTwoShared A
      strategy hwin tag}
    {receiver : ProfiledRawJointHybridShadowPhaseLiveTailLeftReceiver A
      strategy hwin tag}
    (tracked : ProfiledRawJointHybridShadowPhaseLiveTailLeftTracked A strategy
      hwin tag owner receiver)
    (fallback : LeftOutput A strategy hwin tag) (member : Bool)
    (input nextInput : In₁ × In₂) (slot : ProfiledRawRightSlot A)
    (hlive :
      let row :=
        profiledRawJointHybridShadowPhaseLiveTailLeftReceiverRow A strategy
          hwin tag receiver
      let output :=
        (profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStep A strategy
          hwin tag fallback owner receiver input).1
      (output.target row).1.1.family.right () = some slot) :
    let row :=
      profiledRawJointHybridShadowPhaseLiveTailLeftReceiverRow A strategy hwin
        tag receiver
    let result :=
      profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStep A strategy hwin
        tag fallback owner receiver input
    let nextOwner :
        ProfiledRawJointHybridShadowPhaseLiveTailFrontierTwoShared A strategy
          hwin tag :=
      ⟨owner.1,
        (profiledRawJointHybridShadowPhaseLiveTailLeftSharedStep A strategy
          hwin tag owner.1 member owner.2 input.2).1⟩
    pairedLeftClosingForRow row
        (profiledRawJointHybridShadowPhaseLiveTailLeftSingleTableRecord A
          strategy hwin tag fallback nextOwner result.2 nextInput).physical =
      slot.2 (nextInput.2, nextInput.1) := by
  rcases tracked with
    ⟨state, move, ownerControl, row, monitorState, staged, past, rfl, rfl,
      _hmove, _hreachable, _hone, _hroot, hlocal⟩
  simp only [profiledRawJointHybridShadowPhaseLiveTailLeftReceiverRow,
    profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStep_live] at hlive ⊢
  let env : Nat → In₁ × In₂ := omegaOfList (past ++ [input, nextInput])
  have hpast : omegaPrefix env past.length = past := by
    apply List.ext_get
    · simp [env, omegaPrefix]
    · intro n hnLeft hnRight
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [omegaPrefix, List.getElem_ofFn]
      have hnPrefix : n < (past ++ [input, nextInput]).length := by
        simp
        omega
      change omegaOfList (past ++ [input, nextInput]) n = past[n]
      rw [omegaOfList_eq_getElem _ n hnPrefix]
      simp [hnRight]
  have hinput : env past.length = input := by
    simp [env, omegaOfList_eq_getElem]
  have hprefixNext :
      omegaPrefix env (past ++ [input]).length = past ++ [input] := by
    apply List.ext_get
    · simp [env, omegaPrefix]
    · intro n hnLeft hnRight
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [omegaPrefix, List.getElem_ofFn]
      have hnPrefix : n < (past ++ [input, nextInput]).length := by
        simp at hnRight ⊢
        omega
      change omegaOfList (past ++ [input, nextInput]) n =
        (past ++ [input])[n]
      rw [omegaOfList_eq_getElem _ n hnPrefix]
      have hnAppend : n < ((past ++ [input]) ++ [nextInput]).length := by
        simpa [List.append_assoc] using hnPrefix
      simpa [List.append_assoc] using
        (List.getElem_append_left (bs := [nextInput]) hnRight
          (h' := hnAppend))
  have hnextInput : env (past ++ [input]).length = nextInput := by
    simp [env, omegaOfList_eq_getElem]
  have hcurrent := hlocal.output_eq_play_of_prefix A strategy hwin row input env
    hpast hinput
  have hlocalNext := hlocal.step A strategy hwin row input
  have hnext := hlocalNext.output_eq_play_of_prefix A strategy hwin row nextInput
    env hprefixNext hnextInput
  let physicalPlay :=
    profiledRawJointHybridShadowPhaseLiveTailLeftPhysicalPlay A strategy hwin
      tag state move false env
  have hcurrentPhysical :
      profiledRawJointHybridShadowPhaseLiveTailLeftReceiverProjection A
          strategy hwin
          (profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStepFor A
            strategy hwin tag state move ownerControl row monitorState input).1 =
        (physicalPlay past.length).2.1 := by
    simpa [physicalPlay,
      profiledRawJointHybridShadowPhaseLiveTailLeftPhysicalPlay] using
      congrArg
        (profiledRawJointHybridShadowPhaseLiveTailLeftReceiverProjection A
          strategy hwin) hcurrent
  have hlivePhysical :
      ((physicalPlay past.length).2.1.target row).family.right () = some slot := by
    rw [← hcurrentPhysical]
    exact hlive
  have hdelay :=
    profiledRawJointLeftPhysicalSiblingWinningPlay_delayedLiveSlot A move.1
      physicalPlay
      (profiledRawJointHybridShadowPhaseLiveTailLeftPhysicalPlay_wins A
        strategy hwin tag state move false env)
      past.length row slot hlivePhysical
  have hnextPhysical :
      profiledRawJointHybridShadowPhaseLiveTailLeftReceiverProjection A
          strategy hwin
          (profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStepFor A
            strategy hwin tag state move
              ((move.memberController A false).step ownerControl input.2) row
              ((profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStepFor A
                strategy hwin tag state move ownerControl row monitorState
                  input).2.2.get (by rfl)).2.2.1 nextInput).1 =
        (physicalPlay (past.length + 1)).2.1 := by
    simpa [physicalPlay,
      profiledRawJointHybridShadowPhaseLiveTailLeftPhysicalPlay] using
      congrArg
        (profiledRawJointHybridShadowPhaseLiveTailLeftReceiverProjection A
          strategy hwin) hnext
  rw [← hnextPhysical] at hdelay
  have hownerAdvance :=
    (profiledRawJointLeftPhysicalSiblingDeferredStep_laws A move).state_eq
      member false ownerControl input.2
  simp only [profiledRawJointLeftPhysicalSiblingDeferredStep] at hownerAdvance
  have hphysicalInput : (physicalPlay (past.length + 1)).1 = nextInput := by
    change env (past.length + 1) = nextInput
    simpa using hnextInput
  rw [hphysicalInput] at hdelay
  simp only [profiledRawJointHybridShadowPhaseLiveTailLeftSharedStep,
    profiledRawJointLeftPhysicalSiblingDeferredStep]
  rw [hownerAdvance]
  simpa [profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStepFor,
    profiledRawJointHybridShadowPhaseLiveTailLeftReceiverProjection,
    profiledRawJointHybridShadowPhaseLiveTailLeftSingleTableRecord]
    using hdelay

/-! ## A root-aligned key initializes the crossed fresh table -/

/-- The left table installed from a right target uses the target slot as its
descriptor source and therefore emits that profile on its fresh row. -/
theorem
    ProfiledRawJointHybridShadowPhaseLiveTailRightSuccessorKeyAt.freshLeftProfile
    {tag : Tag A strategy hwin}
    {state : ProfiledRawJointHybridShadowPhaseLiveTailState A strategy hwin tag}
    (output : RightOutput A strategy hwin tag) (entryRow : PairedEntryRow)
    (hkey :
      ProfiledRawJointHybridShadowPhaseLiveTailRightSuccessorKeyAt A strategy
        hwin state
          (profiledRawJointHybridShadowPhaseLiveTailSuccessorTargetKey A
            strategy hwin (output.target entryRow).1)
          (output.target entryRow).1.1) :
    ∃ slot : ProfiledRawLeftSlot A,
      (output.target entryRow).1.1.family.left () = some slot ∧
        ∀ (parent :
            ProfiledRawJointHybridShadowPhaseLiveTailFrontierTwoShared A
              strategy hwin tag)
          (fallback : LeftOutput A strategy hwin tag)
          (input : In₁ × In₂),
        let payload :=
          profiledRawJointHybridShadowPhaseLiveTailRightPendingPayloadOfOutput A
            strategy hwin tag output entryRow
        pairedLeftInformedForRow .first
            (profiledRawJointHybridShadowPhaseLiveTailLeftSingleTableRecord A
              strategy hwin tag fallback
                (profiledRawJointHybridShadowPhaseLiveTailFreshLeftOwner A
                  strategy hwin tag parent payload)
                (profiledRawJointHybridShadowPhaseLiveTailFreshLeftReceiver A
                  strategy hwin tag payload false) input).physical =
          slot.2 input := by
  rcases hkey with ⟨slot, hlive, ⟨aligned⟩⟩
  refine ⟨slot, hlive, ?_⟩
  intro parent fallback input
  dsimp only
  obtain ⟨move, hmove, hsource⟩ := aligned.left_move_source A strategy hwin
  let next :=
    profiledRawJointHybridShadowPhaseLiveTailSuccessorTargetKey A strategy hwin
      (output.target entryRow).1
  let env : Nat → In₁ × In₂ := fun _ ↦ input
  let play :=
    profiledRawJointHybridShadowPhaseLiveTailLeftPhysicalPlay A strategy hwin
      tag next move false env
  have hroot := profiledRawJointLeftPhysicalSiblingWinningPlay_rootProfile A
    move.1 play
      (profiledRawJointHybridShadowPhaseLiveTailLeftPhysicalPlay_wins A
        strategy hwin tag next move false env)
  have htargetFalse :=
    profiledRawJointHybridShadowPhaseLiveTailRightPendingPayloadOfOutput_target A
      strategy hwin tag output entryRow false
  have hlocal :=
    profiledRawJointHybridShadowPhaseLiveTailLeftLocallyReachableAt_initial A
      strategy hwin tag next move
  have hread := hlocal.output_eq_play_of_prefix A strategy hwin .first input env
    (by simp [env, omegaPrefix]) (by rfl)
  have hreadPhysical :
      profiledRawJointHybridShadowPhaseLiveTailLeftReceiverProjection A
          strategy hwin
          (profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStepFor A
            strategy hwin tag next move (move.memberController A false).initial
              .first
              (profiledRawJointHybridShadowPhaseLiveTailSuccessorLeftMonitor A
                strategy hwin (tag := tag) move false).initial input).1 =
        (play 0).2.1 := by
    simpa [play,
      profiledRawJointHybridShadowPhaseLiveTailLeftPhysicalPlay] using
      congrArg
        (profiledRawJointHybridShadowPhaseLiveTailLeftReceiverProjection A
          strategy hwin) hread
  rw [← hreadPhysical] at hroot
  rw [hsource] at hroot
  have hplayInput : (play 0).1 = input := by
    rfl
  rw [hplayInput] at hroot
  have hmoveNext : next.1.2.2 = some move := by
    exact hmove
  have hmoveRaw :
      (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
        hwin (output.target entryRow).1).1.2.2 = some move := by
    simpa [next,
      profiledRawJointHybridShadowPhaseLiveTailSuccessorTargetKey] using hmove
  simp only [profiledRawJointHybridShadowPhaseLiveTailFreshLeftOwner,
    profiledRawJointHybridShadowPhaseLiveTailFreshLeftReceiver]
  rw [htargetFalse]
  change pairedLeftInformedForRow .first
      (profiledRawJointHybridShadowPhaseLiveTailLeftSingleTableRecord A
        strategy hwin tag fallback
          ⟨next,
            profiledRawJointHybridShadowPhaseLiveTailLeftSharedInitial A
              strategy hwin tag next⟩
          ⟨next,
            profiledRawJointHybridShadowPhaseLiveTailRightPendingPayloadReceiver
              A strategy hwin tag
                (profiledRawJointHybridShadowPhaseLiveTailRightPendingPayloadOfOutput
                  A strategy hwin tag output entryRow) false⟩ input).physical =
        slot.2 input
  simp [
    profiledRawJointHybridShadowPhaseLiveTailLeftSharedInitial,
    profiledRawJointHybridShadowPhaseLiveTailRightPendingPayloadOfOutput,
    profiledRawJointHybridShadowPhaseLiveTailRightPendingPayloadReceiver,
    profiledRawJointHybridPhysicalCompatibleRightPendingPayloadOfOutput,
    profiledRawJointHybridPhysicalCompatibleRightPendingPayloadReceiver,
    profiledRawJointHybridPhysicalCompatibleLeftPayloadAtRow,
    profiledRawJointHybridShadowPhaseLiveTailLeftReceiverProjection,
    hmoveNext, hmoveRaw] at hroot ⊢
  exact hroot

/-- Right-table mirror of the root-aligned fresh-profile theorem. -/
theorem
    ProfiledRawJointHybridShadowPhaseLiveTailLeftSuccessorKeyAt.freshRightProfile
    {tag : Tag A strategy hwin}
    {state : ProfiledRawJointHybridShadowPhaseLiveTailState A strategy hwin tag}
    (output : LeftOutput A strategy hwin tag) (entryRow : PairedEntryRow)
    (hkey :
      ProfiledRawJointHybridShadowPhaseLiveTailLeftSuccessorKeyAt A strategy
        hwin state
          (profiledRawJointHybridShadowPhaseLiveTailSuccessorTargetKey A
            strategy hwin (output.target entryRow).1)
          (output.target entryRow).1.1) :
    ∃ slot : ProfiledRawRightSlot A,
      (output.target entryRow).1.1.family.right () = some slot ∧
        ∀ (parent :
            ProfiledRawJointHybridShadowPhaseLiveTailFrontierOneShared A
              strategy hwin tag)
          (fallback : RightOutput A strategy hwin tag)
          (input : In₂ × In₁),
        let payload :=
          profiledRawJointHybridShadowPhaseLiveTailLeftPendingPayloadOfOutput A
            strategy hwin tag output entryRow
        pairedRightInformedForRow .first
            (profiledRawJointHybridShadowPhaseLiveTailRightSingleTableRecord A
              strategy hwin tag fallback
                (profiledRawJointHybridShadowPhaseLiveTailFreshRightOwner A
                  strategy hwin tag parent payload)
                (profiledRawJointHybridShadowPhaseLiveTailFreshRightReceiver A
                  strategy hwin tag payload false) input).physical =
          slot.2 input := by
  rcases hkey with ⟨slot, hlive, ⟨aligned⟩⟩
  refine ⟨slot, hlive, ?_⟩
  intro parent fallback input
  dsimp only
  obtain ⟨move, hmove, hsource⟩ := aligned.right_move_source A strategy hwin
  let next :=
    profiledRawJointHybridShadowPhaseLiveTailSuccessorTargetKey A strategy hwin
      (output.target entryRow).1
  let env : Nat → In₂ × In₁ := fun _ ↦ input
  let play :=
    profiledRawJointHybridShadowPhaseLiveTailRightPhysicalPlay A strategy hwin
      tag next move false env
  have hroot := profiledRawJointRightPhysicalSiblingWinningPlay_rootProfile A
    move.1 play
      (profiledRawJointHybridShadowPhaseLiveTailRightPhysicalPlay_wins A
        strategy hwin tag next move false env)
  have htargetFalse :=
    profiledRawJointHybridShadowPhaseLiveTailLeftPendingPayloadOfOutput_target A
      strategy hwin tag output entryRow false
  have hlocal :=
    profiledRawJointHybridShadowPhaseLiveTailRightLocallyReachableAt_initial A
      strategy hwin tag next move
  have hread := hlocal.output_eq_play_of_prefix A strategy hwin .first input env
    (by simp [env, omegaPrefix]) (by rfl)
  have hreadPhysical :
      profiledRawJointHybridShadowPhaseLiveTailRightReceiverProjection A
          strategy hwin
          (profiledRawJointHybridShadowPhaseLiveTailRightReceiverStepFor A
            strategy hwin tag next move (move.memberController A false).initial
              .first
              (profiledRawJointHybridShadowPhaseLiveTailSuccessorRightMonitor A
                strategy hwin (tag := tag) move false).initial input).1 =
        (play 0).2.1 := by
    simpa [play,
      profiledRawJointHybridShadowPhaseLiveTailRightPhysicalPlay] using
      congrArg
        (profiledRawJointHybridShadowPhaseLiveTailRightReceiverProjection A
          strategy hwin) hread
  rw [← hreadPhysical] at hroot
  rw [hsource] at hroot
  have hplayInput : (play 0).1 = input := by
    rfl
  rw [hplayInput] at hroot
  have hmoveNext : next.1.2.1 = some move := by
    exact hmove
  have hmoveRaw :
      (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
        hwin (output.target entryRow).1).1.2.1 = some move := by
    simpa [next,
      profiledRawJointHybridShadowPhaseLiveTailSuccessorTargetKey] using hmove
  simp only [profiledRawJointHybridShadowPhaseLiveTailFreshRightOwner,
    profiledRawJointHybridShadowPhaseLiveTailFreshRightReceiver]
  rw [htargetFalse]
  change pairedRightInformedForRow .first
      (profiledRawJointHybridShadowPhaseLiveTailRightSingleTableRecord A
        strategy hwin tag fallback
          ⟨next,
            profiledRawJointHybridShadowPhaseLiveTailRightSharedInitial A
              strategy hwin tag next⟩
          ⟨next,
            profiledRawJointHybridShadowPhaseLiveTailLeftPendingPayloadReceiver
              A strategy hwin tag
                (profiledRawJointHybridShadowPhaseLiveTailLeftPendingPayloadOfOutput
                  A strategy hwin tag output entryRow) false⟩ input).physical =
        slot.2 input
  simp [profiledRawJointHybridShadowPhaseLiveTailRightSharedInitial,
    profiledRawJointHybridShadowPhaseLiveTailLeftPendingPayloadOfOutput,
    profiledRawJointHybridShadowPhaseLiveTailLeftPendingPayloadReceiver,
    profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadOfOutput,
    profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadReceiver,
    profiledRawJointHybridPhysicalCompatibleRightPayloadAtRow,
    profiledRawJointHybridShadowPhaseLiveTailRightReceiverProjection,
    hmoveNext, hmoveRaw] at hroot ⊢
  exact hroot

/-! ## The two strict constructor fields -/

/-- The corrected strict-right Tail constructor satisfies its row-aware
cross equation from the tracked table alone. -/
theorem
    ProfiledRawJointHybridShadowPhaseLiveTailRowStrictRightConstructorCross_of_tracked
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂)
    (hinvariant :
      ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant A strategy hwin
        tag one two) :
    ProfiledRawJointHybridShadowPhaseLiveTailRowStrictRightConstructorCross A
      strategy hwin tag fallbackLeft fallbackRight one two input := by
  let receiver :=
    profiledRawJointHybridShadowPhaseLiveTailRightReceiverForRecvTwo A strategy
      hwin tag two one
  let row :=
    profiledRawJointHybridShadowPhaseLiveTailRightReceiverRow A strategy hwin tag
      receiver
  let output :=
    (profiledRawJointHybridShadowPhaseLiveTailRightReceiverStep A strategy hwin
      tag fallbackRight one.2.1.baseShared receiver (input.2, input.1)).1
  have htracked := hinvariant.right_selected A strategy hwin
  have hkey := htracked.key A strategy hwin fallbackRight (input.2, input.1)
  obtain ⟨slot, hlive, hfresh⟩ :=
    hkey.freshLeftProfile A strategy hwin output row
  intro nextInput
  have hclosing := htracked.nextClosing_eq_liveTarget A strategy hwin
    fallbackRight one.1 (input.2, input.1) (nextInput.2, nextInput.1) slot
      (by simpa [receiver, row, output] using hlive)
  have hfreshAt := hfresh two.2.1.baseShared fallbackLeft nextInput
  simp only [profiledRawJointHybridShadowPhaseLiveTailSwitchRightRow,
    profiledRawJointHybridShadowPhaseLiveTailSwitchLeftRow]
  rw [profiledRawJointHybridShadowPhaseLiveTailSwitchStrictRightNext_continuedRightRow
    A strategy hwin tag fallbackLeft fallbackRight one two input]
  rw [profiledRawJointHybridShadowPhaseLiveTailSwitchStrictRightNext_freshLeftRow
    A strategy hwin tag fallbackLeft fallbackRight one two input]
  calc
    _ = slot.2 nextInput := by
      simpa [profiledRawJointHybridShadowPhaseLiveTailSwitchStrictRightNext,
        profiledRawJointHybridShadowPhaseLiveTailSwitchRightRecord,
        profiledRawJointHybridShadowPhaseLiveTailRightReceiverForRecvTwo,
        profiledRawJointHybridShadowPhaseLiveTailOnePendingStep,
        FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv,
        FiniteAcknowledgedDelayedCarrier.phaseLivePendingStep,
        profiledRawJointHybridShadowPhaseLiveTailFrontierOnePendingStep,
        FiniteAcknowledgedDelayedCarrier.keyedDeferredSharedStep,
        receiver, row, output] using hclosing
    _ = _ := by
      simpa [profiledRawJointHybridShadowPhaseLiveTailSwitchStrictRightNext,
        profiledRawJointHybridShadowPhaseLiveTailSwitchLeftRecord,
        profiledRawJointHybridShadowPhaseLiveTailLeftReceiverForRecvOne,
        profiledRawJointHybridShadowPhaseLiveTailFreshPair,
        FiniteAcknowledgedDelayedCarrier.PhaseLiveShared.fresh,
        profiledRawJointHybridShadowPhaseLiveTailFreshTwoPayload,
        receiver, row, output] using hfreshAt.symm

/-- Strict-left mirror. -/
theorem
    ProfiledRawJointHybridShadowPhaseLiveTailRowStrictLeftConstructorCross_of_tracked
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂)
    (hinvariant :
      ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant A strategy hwin
        tag one two) :
    ProfiledRawJointHybridShadowPhaseLiveTailRowStrictLeftConstructorCross A
      strategy hwin tag fallbackLeft fallbackRight one two input := by
  let receiver :=
    profiledRawJointHybridShadowPhaseLiveTailLeftReceiverForRecvOne A strategy
      hwin tag one two
  let row :=
    profiledRawJointHybridShadowPhaseLiveTailLeftReceiverRow A strategy hwin tag
      receiver
  let output :=
    (profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStep A strategy hwin
      tag fallbackLeft two.2.1.baseShared receiver input).1
  have htracked := hinvariant.left_selected A strategy hwin
  have hkey := htracked.key A strategy hwin fallbackLeft input
  obtain ⟨slot, hlive, hfresh⟩ :=
    hkey.freshRightProfile A strategy hwin output row
  intro nextInput
  have hclosing := htracked.nextClosing_eq_liveTarget A strategy hwin
    fallbackLeft two.1 input nextInput slot
      (by simpa [receiver, row, output] using hlive)
  have hfreshAt := hfresh one.2.1.baseShared fallbackRight
    (nextInput.2, nextInput.1)
  simp only [profiledRawJointHybridShadowPhaseLiveTailSwitchRightRow,
    profiledRawJointHybridShadowPhaseLiveTailSwitchLeftRow]
  rw [profiledRawJointHybridShadowPhaseLiveTailSwitchStrictLeftNext_continuedLeftRow
    A strategy hwin tag fallbackLeft fallbackRight one two input]
  rw [profiledRawJointHybridShadowPhaseLiveTailSwitchStrictLeftNext_freshRightRow
    A strategy hwin tag fallbackLeft fallbackRight one two input]
  calc
    _ = slot.2 (nextInput.2, nextInput.1) := by
      simpa [profiledRawJointHybridShadowPhaseLiveTailSwitchStrictLeftNext,
        profiledRawJointHybridShadowPhaseLiveTailSwitchLeftRecord,
        profiledRawJointHybridShadowPhaseLiveTailLeftReceiverForRecvOne,
        profiledRawJointHybridShadowPhaseLiveTailTwoPendingStep,
        FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv,
        FiniteAcknowledgedDelayedCarrier.phaseLivePendingStep,
        profiledRawJointHybridShadowPhaseLiveTailFrontierTwoPendingStep,
        FiniteAcknowledgedDelayedCarrier.keyedDeferredSharedStep,
        receiver, row, output] using hclosing
    _ = _ := by
      simpa [profiledRawJointHybridShadowPhaseLiveTailSwitchStrictLeftNext,
        profiledRawJointHybridShadowPhaseLiveTailSwitchRightRecord,
        profiledRawJointHybridShadowPhaseLiveTailRightReceiverForRecvTwo,
        profiledRawJointHybridShadowPhaseLiveTailFreshPair,
        FiniteAcknowledgedDelayedCarrier.PhaseLiveShared.fresh,
        profiledRawJointHybridShadowPhaseLiveTailFreshOnePayload,
        receiver, row, output] using hfreshAt.symm

end

end DetParityAutomaton

end DistributedSynthesis
