/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorLocalReachability

/-!
# Literal-prefix reachability for compatible successor tables

The finite local controls only retain folds of a block prefix.  The physical
cut proof additionally needs to know that the folded prefix is the literal
environment slice since the last installation, rather than merely some word
with the same finite folds.

The predicates below are proof-side refinements of the existing existential
reachability predicates.  They start at the empty prefix and append the
actual local input at every strict step.  No prefix, clock, graph direction,
hierarchy side, leader bit, or strict-leader bit is added to an executable
control.
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

/-! ## Right tables -/

/-- The right owner and monitor are the two literal folds of `past`. -/
def ProfiledRawJointHybridPhysicalCompatibleRightLocallyReachableAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A
        strategy hwin (initial := initial) move false).State)
    (past : List (In₂ × In₁)) : Prop :=
  owner = (move.memberController A false).controlAt (senderWord past) ∧
    monitorState = narrowedControl
      (profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A
        strategy hwin (initial := initial) move false)
      (profiledRawJointHybridPhysicalCompatibleDecoratedRightMemberController
        A strategy hwin policy state move false).labeledTree past

/-- Forget the named word and recover the old existential reachability fact. -/
theorem
    ProfiledRawJointHybridPhysicalCompatibleRightLocallyReachableAt.toLocallyReachable
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {state : CompatibleState A strategy hwin initial}
    {move : ProfiledRawJointRightPhysicalSiblingMove A}
    {owner : (move.memberController A false).Control}
    {monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A
        strategy hwin (initial := initial) move false).State}
    {past : List (In₂ × In₁)}
    (hreach :
      ProfiledRawJointHybridPhysicalCompatibleRightLocallyReachableAt A
        strategy hwin policy state move owner monitorState past) :
    ProfiledRawJointHybridPhysicalCompatibleRightLocallyReachable A strategy
      hwin policy state move owner monitorState :=
  ⟨past, hreach.1, hreach.2⟩

/-- A newly installed right table is at the empty literal prefix. -/
theorem
    profiledRawJointHybridPhysicalCompatibleRightLocallyReachableAt_initial
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointRightPhysicalSiblingMove A) :
    ProfiledRawJointHybridPhysicalCompatibleRightLocallyReachableAt A
      strategy hwin policy state move
        (move.memberController A false).initial
        (profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A
          strategy hwin (initial := initial) move false).initial [] := by
  exact ⟨rfl, rfl⟩

/-- A strict-right local step appends the actual input pair. -/
theorem
    ProfiledRawJointHybridPhysicalCompatibleRightLocallyReachableAt.step
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {state : CompatibleState A strategy hwin initial}
    {move : ProfiledRawJointRightPhysicalSiblingMove A}
    {owner : (move.memberController A false).Control}
    {monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A
        strategy hwin (initial := initial) move false).State}
    {past : List (In₂ × In₁)}
    (hreach :
      ProfiledRawJointHybridPhysicalCompatibleRightLocallyReachableAt A
        strategy hwin policy state move owner monitorState past)
    (row : PairedEntryRow) (input : In₂ × In₁) :
    let result :=
      profiledRawJointHybridPhysicalCompatibleRightReceiverStepFor A strategy
        hwin policy state move owner row monitorState input
    ProfiledRawJointHybridPhysicalCompatibleRightLocallyReachableAt A strategy
      hwin policy state move
        ((move.memberController A false).step owner input.2)
        result.2.2.2.1 (past ++ [input]) := by
  rcases hreach with ⟨rfl, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [senderWord_append, TransitionRationalTree.controlAt_append]
    simp
  · rw [narrowedControl_append]
    rfl

/-- With a named literal prefix, the emitted decorated output is the exact
table-play output at the next position of that same prefix. -/
theorem
    ProfiledRawJointHybridPhysicalCompatibleRightLocallyReachableAt.output_eq_play
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {state : CompatibleState A strategy hwin initial}
    {move : ProfiledRawJointRightPhysicalSiblingMove A}
    {owner : (move.memberController A false).Control}
    {monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A
        strategy hwin (initial := initial) move false).State}
    {past : List (In₂ × In₁)}
    (hreach :
      ProfiledRawJointHybridPhysicalCompatibleRightLocallyReachableAt A
        strategy hwin policy state move owner monitorState past)
    (tableMember : Bool) (row : PairedEntryRow) (input : In₂ × In₁) :
    (profiledRawJointHybridPhysicalCompatibleRightReceiverStepFor A strategy
        hwin policy state move owner row monitorState input).1 =
      (profiledRawJointHybridPhysicalCompatibleRightDecoratedPlay A strategy
        hwin policy state move tableMember
          (omegaOfList (past ++ [input])) past.length).2.1 := by
  rcases hreach with ⟨howner, hmonitor⟩
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

/-! ## Left tables -/

/-- Left-table mirror of literal-prefix reachability. -/
def ProfiledRawJointHybridPhysicalCompatibleLeftLocallyReachableAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A strategy
        hwin (initial := initial) move false).State)
    (past : List (In₁ × In₂)) : Prop :=
  owner = (move.memberController A false).controlAt (senderWord past) ∧
    monitorState = narrowedControl
      (profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A strategy
        hwin (initial := initial) move false)
      (profiledRawJointHybridPhysicalCompatibleDecoratedLeftMemberController A
        strategy hwin policy state move false).labeledTree past

theorem
    ProfiledRawJointHybridPhysicalCompatibleLeftLocallyReachableAt.toLocallyReachable
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {state : CompatibleState A strategy hwin initial}
    {move : ProfiledRawJointLeftPhysicalSiblingMove A}
    {owner : (move.memberController A false).Control}
    {monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A strategy
        hwin (initial := initial) move false).State}
    {past : List (In₁ × In₂)}
    (hreach :
      ProfiledRawJointHybridPhysicalCompatibleLeftLocallyReachableAt A strategy
        hwin policy state move owner monitorState past) :
    ProfiledRawJointHybridPhysicalCompatibleLeftLocallyReachable A strategy
      hwin policy state move owner monitorState :=
  ⟨past, hreach.1, hreach.2⟩

theorem
    profiledRawJointHybridPhysicalCompatibleLeftLocallyReachableAt_initial
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A) :
    ProfiledRawJointHybridPhysicalCompatibleLeftLocallyReachableAt A strategy
      hwin policy state move (move.memberController A false).initial
        (profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A strategy
          hwin (initial := initial) move false).initial [] := by
  exact ⟨rfl, rfl⟩

theorem
    ProfiledRawJointHybridPhysicalCompatibleLeftLocallyReachableAt.step
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {state : CompatibleState A strategy hwin initial}
    {move : ProfiledRawJointLeftPhysicalSiblingMove A}
    {owner : (move.memberController A false).Control}
    {monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A strategy
        hwin (initial := initial) move false).State}
    {past : List (In₁ × In₂)}
    (hreach :
      ProfiledRawJointHybridPhysicalCompatibleLeftLocallyReachableAt A strategy
        hwin policy state move owner monitorState past)
    (row : PairedEntryRow) (input : In₁ × In₂) :
    let result :=
      profiledRawJointHybridPhysicalCompatibleLeftReceiverStepFor A strategy
        hwin policy state move owner row monitorState input
    ProfiledRawJointHybridPhysicalCompatibleLeftLocallyReachableAt A strategy
      hwin policy state move ((move.memberController A false).step owner input.2)
        result.2.2.2.1 (past ++ [input]) := by
  rcases hreach with ⟨rfl, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [senderWord_append, TransitionRationalTree.controlAt_append]
    simp
  · rw [narrowedControl_append]
    rfl

theorem
    ProfiledRawJointHybridPhysicalCompatibleLeftLocallyReachableAt.output_eq_play
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {state : CompatibleState A strategy hwin initial}
    {move : ProfiledRawJointLeftPhysicalSiblingMove A}
    {owner : (move.memberController A false).Control}
    {monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A strategy
        hwin (initial := initial) move false).State}
    {past : List (In₁ × In₂)}
    (hreach :
      ProfiledRawJointHybridPhysicalCompatibleLeftLocallyReachableAt A strategy
        hwin policy state move owner monitorState past)
    (tableMember : Bool) (row : PairedEntryRow) (input : In₁ × In₂) :
    (profiledRawJointHybridPhysicalCompatibleLeftReceiverStepFor A strategy
        hwin policy state move owner row monitorState input).1 =
      (profiledRawJointHybridPhysicalCompatibleLeftDecoratedPlay A strategy
        hwin policy state move tableMember
          (omegaOfList (past ++ [input])) past.length).2.1 := by
  rcases hreach with ⟨howner, hmonitor⟩
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

end

end DetParityAutomaton

end DistributedSynthesis
