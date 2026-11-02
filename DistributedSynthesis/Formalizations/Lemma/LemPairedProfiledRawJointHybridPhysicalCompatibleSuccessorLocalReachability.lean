/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorDeferredHandlers
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorReceiverMemberIndependence

/-!
# Matched-prefix reachability of compatible successor tables

An installed owner control and its crossed receiver monitor must be the two
folds of one finite input prefix of the same decorated table.  The prefix in
this file is proof-side evidence only; it is never stored by an endpoint and
does not reveal a graph orientation or strict leader.
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

private abbrev CompatiblePolicy
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleRationalPolicy A strategy hwin
    initial

private abbrev CompatibleState
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatiblePolicyState A strategy hwin initial

/-! ## Right-table matched prefixes -/

def ProfiledRawJointHybridPhysicalCompatibleRightLocallyReachable
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A strategy
        hwin (initial := initial) move false).State) : Prop :=
  ∃ past : List (In₂ × In₁),
    owner = (move.memberController A false).controlAt (senderWord past) ∧
      monitorState = narrowedControl
        (profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A
          strategy hwin (initial := initial) move false)
        (profiledRawJointHybridPhysicalCompatibleDecoratedRightMemberController
          A strategy hwin policy state move false).labeledTree past

theorem profiledRawJointHybridPhysicalCompatibleRightLocallyReachable_initial
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointRightPhysicalSiblingMove A) :
    ProfiledRawJointHybridPhysicalCompatibleRightLocallyReachable A strategy
      hwin policy state move (move.memberController A false).initial
      (profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A strategy
        hwin (initial := initial) move false).initial := by
  exact ⟨[], rfl, rfl⟩

theorem
    ProfiledRawJointHybridPhysicalCompatibleRightLocallyReachable.step
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {state : CompatibleState A strategy hwin initial}
    {move : ProfiledRawJointRightPhysicalSiblingMove A}
    {owner : (move.memberController A false).Control}
    {monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A strategy
        hwin (initial := initial) move false).State}
    (hreach :
      ProfiledRawJointHybridPhysicalCompatibleRightLocallyReachable A strategy
        hwin policy state move owner monitorState)
    (row : PairedEntryRow) (input : In₂ × In₁) :
    let result :=
      profiledRawJointHybridPhysicalCompatibleRightReceiverStepFor A strategy
        hwin policy state move owner row monitorState input
    ProfiledRawJointHybridPhysicalCompatibleRightLocallyReachable A strategy
      hwin policy state move
        ((move.memberController A false).step owner input.2)
        result.2.2.2.1 := by
  rcases hreach with ⟨past, rfl, rfl⟩
  refine ⟨past ++ [input], ?_, ?_⟩
  · rw [senderWord_append, TransitionRationalTree.controlAt_append]
    simp
  · rw [narrowedControl_append]
    rfl

theorem
    ProfiledRawJointHybridPhysicalCompatibleRightLocallyReachable.exists_output_eq_play
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {state : CompatibleState A strategy hwin initial}
    {move : ProfiledRawJointRightPhysicalSiblingMove A}
    {owner : (move.memberController A false).Control}
    {monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A strategy
        hwin (initial := initial) move false).State}
    (hreach :
      ProfiledRawJointHybridPhysicalCompatibleRightLocallyReachable A strategy
        hwin policy state move owner monitorState)
    (tableMember : Bool) (row : PairedEntryRow) (input : In₂ × In₁) :
    ∃ past : List (In₂ × In₁),
      owner = (move.memberController A false).controlAt (senderWord past) ∧
      monitorState = narrowedControl
        (profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A
          strategy hwin (initial := initial) move false)
        (profiledRawJointHybridPhysicalCompatibleDecoratedRightMemberController
          A strategy hwin policy state move false).labeledTree past ∧
      (profiledRawJointHybridPhysicalCompatibleRightReceiverStepFor A strategy
          hwin policy state move owner row monitorState input).1 =
        (profiledRawJointHybridPhysicalCompatibleRightDecoratedPlay A strategy
          hwin policy state move tableMember
          (omegaOfList (past ++ [input])) past.length).2.1 := by
  rcases hreach with ⟨past, howner, hmonitor⟩
  refine ⟨past, howner, hmonitor, ?_⟩
  subst owner
  subst monitorState
  let env : Nat → In₂ × In₁ := omegaOfList (past ++ [input])
  have hpast : omegaPrefix env past.length = past := by
    apply List.ext_get
    · simp [omegaPrefix]
    · intro n hnLeft hnRight
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [omegaPrefix, List.getElem_ofFn]
      have hnPrefix : n < (past ++ [input]).length := by simp; omega
      change omegaOfList (past ++ [input]) n = past[n]
      rw [omegaOfList_eq_getElem (past ++ [input]) n hnPrefix]
      simp [hnRight]
  have hinput : env past.length = input := by
    have hnPrefix : past.length < (past ++ [input]).length := by simp
    change omegaOfList (past ++ [input]) past.length = input
    rw [omegaOfList_eq_getElem (past ++ [input]) past.length hnPrefix]
    simp
  cases tableMember <;>
    simp [profiledRawJointHybridPhysicalCompatibleRightDecoratedPlay,
      profiledRawJointHybridPhysicalCompatibleRightReceiverStepFor,
      treePlay, narrowedInducedTree, blockLabelApply, narrowedRecord,
      TransitionRationalTree.labeledTree, branchNode_eq_omegaPrefix,
      hpast, hinput, env]
  all_goals rfl

/-! ## Left-table mirror -/

def ProfiledRawJointHybridPhysicalCompatibleLeftLocallyReachable
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A strategy
        hwin (initial := initial) move false).State) : Prop :=
  ∃ past : List (In₁ × In₂),
    owner = (move.memberController A false).controlAt (senderWord past) ∧
      monitorState = narrowedControl
        (profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A
          strategy hwin (initial := initial) move false)
        (profiledRawJointHybridPhysicalCompatibleDecoratedLeftMemberController
          A strategy hwin policy state move false).labeledTree past

theorem profiledRawJointHybridPhysicalCompatibleLeftLocallyReachable_initial
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A) :
    ProfiledRawJointHybridPhysicalCompatibleLeftLocallyReachable A strategy
      hwin policy state move (move.memberController A false).initial
      (profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A strategy
        hwin (initial := initial) move false).initial := by
  exact ⟨[], rfl, rfl⟩

theorem
    ProfiledRawJointHybridPhysicalCompatibleLeftLocallyReachable.step
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {state : CompatibleState A strategy hwin initial}
    {move : ProfiledRawJointLeftPhysicalSiblingMove A}
    {owner : (move.memberController A false).Control}
    {monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A strategy
        hwin (initial := initial) move false).State}
    (hreach :
      ProfiledRawJointHybridPhysicalCompatibleLeftLocallyReachable A strategy
        hwin policy state move owner monitorState)
    (row : PairedEntryRow) (input : In₁ × In₂) :
    let result :=
      profiledRawJointHybridPhysicalCompatibleLeftReceiverStepFor A strategy
        hwin policy state move owner row monitorState input
    ProfiledRawJointHybridPhysicalCompatibleLeftLocallyReachable A strategy
      hwin policy state move
        ((move.memberController A false).step owner input.2)
        result.2.2.2.1 := by
  rcases hreach with ⟨past, rfl, rfl⟩
  refine ⟨past ++ [input], ?_, ?_⟩
  · rw [senderWord_append, TransitionRationalTree.controlAt_append]
    simp
  · rw [narrowedControl_append]
    rfl

theorem
    ProfiledRawJointHybridPhysicalCompatibleLeftLocallyReachable.exists_output_eq_play
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {state : CompatibleState A strategy hwin initial}
    {move : ProfiledRawJointLeftPhysicalSiblingMove A}
    {owner : (move.memberController A false).Control}
    {monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A strategy
        hwin (initial := initial) move false).State}
    (hreach :
      ProfiledRawJointHybridPhysicalCompatibleLeftLocallyReachable A strategy
        hwin policy state move owner monitorState)
    (tableMember : Bool) (row : PairedEntryRow) (input : In₁ × In₂) :
    ∃ past : List (In₁ × In₂),
      owner = (move.memberController A false).controlAt (senderWord past) ∧
      monitorState = narrowedControl
        (profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A
          strategy hwin (initial := initial) move false)
        (profiledRawJointHybridPhysicalCompatibleDecoratedLeftMemberController
          A strategy hwin policy state move false).labeledTree past ∧
      (profiledRawJointHybridPhysicalCompatibleLeftReceiverStepFor A strategy
          hwin policy state move owner row monitorState input).1 =
        (profiledRawJointHybridPhysicalCompatibleLeftDecoratedPlay A strategy
          hwin policy state move tableMember
          (omegaOfList (past ++ [input])) past.length).2.1 := by
  rcases hreach with ⟨past, howner, hmonitor⟩
  refine ⟨past, howner, hmonitor, ?_⟩
  subst owner
  subst monitorState
  let env : Nat → In₁ × In₂ := omegaOfList (past ++ [input])
  have hpast : omegaPrefix env past.length = past := by
    apply List.ext_get
    · simp [omegaPrefix]
    · intro n hnLeft hnRight
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [omegaPrefix, List.getElem_ofFn]
      have hnPrefix : n < (past ++ [input]).length := by simp; omega
      change omegaOfList (past ++ [input]) n = past[n]
      rw [omegaOfList_eq_getElem (past ++ [input]) n hnPrefix]
      simp [hnRight]
  have hinput : env past.length = input := by
    have hnPrefix : past.length < (past ++ [input]).length := by simp
    change omegaOfList (past ++ [input]) past.length = input
    rw [omegaOfList_eq_getElem (past ++ [input]) past.length hnPrefix]
    simp
  cases tableMember <;>
    simp [profiledRawJointHybridPhysicalCompatibleLeftDecoratedPlay,
      profiledRawJointHybridPhysicalCompatibleLeftReceiverStepFor,
      treePlay, narrowedInducedTree, blockLabelApply, narrowedRecord,
      TransitionRationalTree.labeledTree, branchNode_eq_omegaPrefix,
      hpast, hinput, env]
  all_goals rfl

/-! ## Direct connection to the concrete deferred receive handlers -/

private abbrev ReachOneShared
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  ProfiledRawJointHybridPhysicalCompatibleFrontierOneShared.{u, v, x, y, s,
    max u v x y s} A strategy hwin policy

private abbrev ReachTwoShared
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  ProfiledRawJointHybridPhysicalCompatibleFrontierTwoShared.{u, v, x, y, s,
    max u v x y s} A strategy hwin policy

private abbrev ReachOneControl
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  ProfiledRawJointHybridPhysicalCompatibleFrontierOneControl.{u, v, x, y, s,
    max u v x y s, 0} A strategy hwin policy

private abbrev ReachTwoControl
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  ProfiledRawJointHybridPhysicalCompatibleFrontierTwoControl.{u, v, x, y, s,
    max u v x y s, 0} A strategy hwin policy

/-- A live installed right receiver plus the matched-prefix invariant
discharges the exact one-cut equality expected by the packet adapter. -/
theorem
    profiledRawJointHybridPhysicalCompatibleFrontierTwoReceiver_eq_play_of_reachable
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (fallback : PairedEntryRow ×
      ProfiledRawJointHybridPhysicalCompatibleSuccessorRightReceiverOutput A
        strategy hwin initial)
    (two : ReachTwoControl A strategy hwin policy) (inputTwo : In₂)
    (pending : FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
      (ReachOneShared A strategy hwin policy)
      (ProfiledRawJointHybridPhysicalCompatibleFrontierOnePayload A strategy
        hwin (initial := initial)))
    (inputOne : In₁)
    (state : CompatibleState A strategy hwin initial) (member : Bool)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (row : PairedEntryRow)
    (monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A strategy
        hwin (initial := initial) move false).State)
    (staged : Option
      (ProfiledRawJointHybridPhysicalCompatibleSuccessorRightReceiverOutput A
        strategy hwin initial))
    (hinstalled :
      profiledRawJointHybridPhysicalCompatibleInstallRightPendingMember.{u, v,
        x, y, s, max u v x y s, max u v x y s} A strategy hwin policy pending =
        ((⟨state, member, .inr ⟨move, owner⟩⟩),
          some ⟨move, row, monitorState, staged⟩))
    (hreach :
      ProfiledRawJointHybridPhysicalCompatibleRightLocallyReachable A strategy
        hwin policy state move owner monitorState)
    (tableMember : Bool) :
    ∃ past : List (In₂ × In₁),
      profiledRawJointHybridPhysicalCompatibleFrontierTwoReceiver A strategy
          hwin policy fallback two inputTwo (.inl pending) inputOne =
        (row,
          (profiledRawJointHybridPhysicalCompatibleRightDecoratedPlay A
            strategy hwin policy state move tableMember
              (omegaOfList (past ++ [(inputTwo, inputOne)])) past.length).2.1) := by
  obtain ⟨past, _, _, houtput⟩ :=
    hreach.exists_output_eq_play A strategy hwin tableMember row
      (inputTwo, inputOne)
  refine ⟨past, ?_⟩
  rw [profiledRawJointHybridPhysicalCompatibleFrontierTwoReceiver_of_installed
    A strategy hwin policy fallback two inputTwo pending inputOne state member
      move owner row monitorState staged hinstalled, houtput]

/-- Process-one/left-table mirror. -/
theorem
    profiledRawJointHybridPhysicalCompatibleFrontierOneReceiver_eq_play_of_reachable
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (fallback : PairedEntryRow ×
      ProfiledRawJointHybridPhysicalCompatibleSuccessorLeftReceiverOutput A
        strategy hwin initial)
    (one : ReachOneControl A strategy hwin policy) (inputOne : In₁)
    (pending : FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
      (ReachTwoShared A strategy hwin policy)
      (ProfiledRawJointHybridPhysicalCompatibleFrontierTwoPayload A strategy
        hwin (initial := initial)))
    (inputTwo : In₂)
    (state : CompatibleState A strategy hwin initial) (member : Bool)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (row : PairedEntryRow)
    (monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A strategy
        hwin (initial := initial) move false).State)
    (staged : Option
      (ProfiledRawJointHybridPhysicalCompatibleSuccessorLeftReceiverOutput A
        strategy hwin initial))
    (hinstalled :
      profiledRawJointHybridPhysicalCompatibleInstallLeftPendingMember.{u, v,
        x, y, s, max u v x y s, max u v x y s} A strategy hwin policy pending =
        ((⟨state, member, .inr ⟨move, owner⟩⟩),
          some ⟨move, row, monitorState, staged⟩))
    (hreach :
      ProfiledRawJointHybridPhysicalCompatibleLeftLocallyReachable A strategy
        hwin policy state move owner monitorState)
    (tableMember : Bool) :
    ∃ past : List (In₁ × In₂),
      profiledRawJointHybridPhysicalCompatibleFrontierOneReceiver A strategy
          hwin policy fallback one inputOne (.inl pending) inputTwo =
        (row,
          (profiledRawJointHybridPhysicalCompatibleLeftDecoratedPlay A strategy
            hwin policy state move tableMember
              (omegaOfList (past ++ [(inputOne, inputTwo)])) past.length).2.1) := by
  obtain ⟨past, _, _, houtput⟩ :=
    hreach.exists_output_eq_play A strategy hwin tableMember row
      (inputOne, inputTwo)
  refine ⟨past, ?_⟩
  rw [profiledRawJointHybridPhysicalCompatibleFrontierOneReceiver_of_installed
    A strategy hwin policy fallback one inputOne pending inputTwo state member
      move owner row monitorState staged hinstalled, houtput]

end

end DetParityAutomaton

end DistributedSynthesis
