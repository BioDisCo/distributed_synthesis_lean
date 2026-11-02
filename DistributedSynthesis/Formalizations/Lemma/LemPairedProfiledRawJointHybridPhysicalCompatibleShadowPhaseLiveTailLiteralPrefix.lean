/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailMemberCutPacket
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailSingleTableBoth

/-!
# Literal table prefixes in a delayed-tag tail fibre

Sharing a tail key and physical move is not by itself enough for a block
certificate: the owner control and receiver monitor must be the two folds of
one literal input prefix.  This file records that stronger proof-side
invariant for the re-rooted tagged tail.  It starts at the empty table prefix,
appends the actual local input pair, and identifies every emitted decorated
record with the corresponding cell of the tag-relative table play.

The prefix and all cut indices occur only in propositions.  Executable local
controls remain the finite sender and monitor folds and receive no graph,
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

private abbrev PhysicalWord :=
  OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂)

/-! ## Right local folds -/

/-- The owner and receiver monitor are precisely the folds of `past` in one
right table of the fixed tagged-tail state. -/
def ProfiledRawJointHybridShadowPhaseLiveTailRightLocallyReachableAt
    (tag : Tag A strategy hwin) (state : TailState A strategy hwin tag)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (monitorState :
      (profiledRawJointHybridShadowPhaseLiveTailSuccessorRightMonitor A
        strategy hwin (tag := tag) move false).State)
    (past : List (In₂ × In₁)) : Prop :=
  owner = (move.memberController A false).controlAt (senderWord past) ∧
    monitorState = narrowedControl
      (profiledRawJointHybridShadowPhaseLiveTailSuccessorRightMonitor A
        strategy hwin (tag := tag) move false)
      (profiledRawJointHybridShadowPhaseLiveTailDecoratedRightMemberController A
        strategy hwin state move false).labeledTree past

theorem
    profiledRawJointHybridShadowPhaseLiveTailRightLocallyReachableAt_initial
    (tag : Tag A strategy hwin) (state : TailState A strategy hwin tag)
    (move : ProfiledRawJointRightPhysicalSiblingMove A) :
    ProfiledRawJointHybridShadowPhaseLiveTailRightLocallyReachableAt A strategy
      hwin tag state move (move.memberController A false).initial
        (profiledRawJointHybridShadowPhaseLiveTailSuccessorRightMonitor A
          strategy hwin (tag := tag) move false).initial [] :=
  ⟨rfl, rfl⟩

theorem
    ProfiledRawJointHybridShadowPhaseLiveTailRightLocallyReachableAt.step
    {tag : Tag A strategy hwin} {state : TailState A strategy hwin tag}
    {move : ProfiledRawJointRightPhysicalSiblingMove A}
    {owner : (move.memberController A false).Control}
    {monitorState :
      (profiledRawJointHybridShadowPhaseLiveTailSuccessorRightMonitor A
        strategy hwin (tag := tag) move false).State}
    {past : List (In₂ × In₁)}
    (hreach :
      ProfiledRawJointHybridShadowPhaseLiveTailRightLocallyReachableAt A
        strategy hwin tag state move owner monitorState past)
    (row : PairedEntryRow) (input : In₂ × In₁) :
    let result :=
      profiledRawJointHybridShadowPhaseLiveTailRightReceiverStepFor A strategy
        hwin tag state move owner row monitorState input
    ProfiledRawJointHybridShadowPhaseLiveTailRightLocallyReachableAt A strategy
      hwin tag state move ((move.memberController A false).step owner input.2)
        (result.2.2.get (by rfl)).2.2.1 (past ++ [input]) := by
  rcases hreach with ⟨rfl, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [senderWord_append, TransitionRationalTree.controlAt_append]
    simp
  · rw [narrowedControl_append]
    rfl

/-- A local receiver calculation at a literal prefix is exactly the next
cell of the tag-relative decorated play. -/
theorem
    ProfiledRawJointHybridShadowPhaseLiveTailRightLocallyReachableAt.output_eq_play
    {tag : Tag A strategy hwin} {state : TailState A strategy hwin tag}
    {move : ProfiledRawJointRightPhysicalSiblingMove A}
    {owner : (move.memberController A false).Control}
    {monitorState :
      (profiledRawJointHybridShadowPhaseLiveTailSuccessorRightMonitor A
        strategy hwin (tag := tag) move false).State}
    {past : List (In₂ × In₁)}
    (hreach :
      ProfiledRawJointHybridShadowPhaseLiveTailRightLocallyReachableAt A
        strategy hwin tag state move owner monitorState past)
    (tableMember : Bool) (row : PairedEntryRow) (input : In₂ × In₁) :
    (profiledRawJointHybridShadowPhaseLiveTailRightReceiverStepFor A strategy
        hwin tag state move owner row monitorState input).1 =
      (profiledRawJointHybridShadowPhaseLiveTailRightDecoratedPlay A strategy
        hwin tag state move tableMember (omegaOfList (past ++ [input]))
          past.length).2.1 := by
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
  cases tableMember <;>
    simp [profiledRawJointHybridShadowPhaseLiveTailRightDecoratedPlay,
      profiledRawJointHybridShadowPhaseLiveTailRightReceiverStepFor,
      treePlay, narrowedInducedTree, blockLabelApply,
      TransitionRationalTree.labeledTree, branchNode_eq_omegaPrefix,
      hpast, env]
  all_goals rfl

/-! ## Right literal physical segments -/

structure ProfiledRawJointHybridShadowPhaseLiveTailRightLiteralPrefixAt
    (tag : Tag A strategy hwin) (state : TailState A strategy hwin tag)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (tableMember : Bool) (row : PairedEntryRow)
    (localEnv : Nat → In₂ × In₁)
    (owner : (move.memberController A false).Control)
    (monitorState :
      (profiledRawJointHybridShadowPhaseLiveTailSuccessorRightMonitor A
        strategy hwin (tag := tag) move false).State)
    (word : PhysicalWord (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂))
    (start n : Nat) : Prop where
  literal_reachable :
    ProfiledRawJointHybridShadowPhaseLiveTailRightLocallyReachableAt A strategy
      hwin tag state move owner monitorState (omegaPrefix localEnv n)
  records :
    omegaPrefix (OmegaWord.drop word start) n =
      profiledRawJointTargetRightPhysicalPrefixRecords A row
        (omegaPrefix
          (profiledRawJointHybridShadowPhaseLiveTailRightPhysicalPlay A strategy
            hwin tag state move tableMember localEnv) n)

namespace ProfiledRawJointHybridShadowPhaseLiveTailRightLiteralPrefixAt

theorem initial
    (tag : Tag A strategy hwin) (state : TailState A strategy hwin tag)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (tableMember : Bool) (row : PairedEntryRow)
    (localEnv : Nat → In₂ × In₁)
    (word : PhysicalWord (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)) (start : Nat) :
    ProfiledRawJointHybridShadowPhaseLiveTailRightLiteralPrefixAt A strategy
      hwin tag state move tableMember row localEnv
        (move.memberController A false).initial
        (profiledRawJointHybridShadowPhaseLiveTailSuccessorRightMonitor A
          strategy hwin (tag := tag) move false).initial word start 0 :=
  ⟨profiledRawJointHybridShadowPhaseLiveTailRightLocallyReachableAt_initial A
      strategy hwin tag state move, rfl⟩

theorem step
    {tag : Tag A strategy hwin} {state : TailState A strategy hwin tag}
    {move : ProfiledRawJointRightPhysicalSiblingMove A}
    {tableMember : Bool} {row : PairedEntryRow}
    {localEnv : Nat → In₂ × In₁}
    {owner : (move.memberController A false).Control}
    {monitorState :
      (profiledRawJointHybridShadowPhaseLiveTailSuccessorRightMonitor A
        strategy hwin (tag := tag) move false).State}
    {word : PhysicalWord (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {start n : Nat}
    (segment :
      ProfiledRawJointHybridShadowPhaseLiveTailRightLiteralPrefixAt A strategy
        hwin tag state move tableMember row localEnv owner monitorState word
          start n)
    (hrecord : word (start + n) =
      pairedRightRecordForRow row
        (profiledRawJointTargetRightPhysicalLetter A
          (profiledRawJointHybridShadowPhaseLiveTailRightPhysicalPlay A strategy
            hwin tag state move tableMember localEnv n))) :
    let result :=
      profiledRawJointHybridShadowPhaseLiveTailRightReceiverStepFor A strategy
        hwin tag state move owner row monitorState (localEnv n)
    ProfiledRawJointHybridShadowPhaseLiveTailRightLiteralPrefixAt A strategy
      hwin tag state move tableMember row localEnv
        ((move.memberController A false).step owner (localEnv n).2)
        (result.2.2.get (by rfl)).2.2.1 word start (n + 1) := by
  dsimp only
  constructor
  · simpa only [omegaPrefix_succ] using
      segment.literal_reachable.step A strategy hwin row (localEnv n)
  · rw [omegaPrefix_succ, omegaPrefix_succ, segment.records]
    simp only [OmegaWord.drop]
    rw [hrecord]
    simp [profiledRawJointTargetRightPhysicalPrefixRecords]

/-- Extract precisely the length and slice equations consumed by the cut
packet, with no schedule-specific wrapper. -/
theorem cutPrefix
    {tag : Tag A strategy hwin} {state : TailState A strategy hwin tag}
    {move : ProfiledRawJointRightPhysicalSiblingMove A}
    {tableMember : Bool} {row : PairedEntryRow}
    {localEnv : Nat → In₂ × In₁}
    {owner : (move.memberController A false).Control}
    {monitorState :
      (profiledRawJointHybridShadowPhaseLiveTailSuccessorRightMonitor A
        strategy hwin (tag := tag) move false).State}
    {word : PhysicalWord (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {start n : Nat}
    (segment :
      ProfiledRawJointHybridShadowPhaseLiveTailRightLiteralPrefixAt A strategy
        hwin tag state move tableMember row localEnv owner monitorState word
          start n) :
    (profiledRawJointTargetRightPhysicalPrefixRecords A row
        (omegaPrefix
          (profiledRawJointHybridShadowPhaseLiveTailRightPhysicalPlay A strategy
            hwin tag state move tableMember localEnv) n)).length = n ∧
      omegaPrefix (OmegaWord.drop word start)
          (profiledRawJointTargetRightPhysicalPrefixRecords A row
            (omegaPrefix
              (profiledRawJointHybridShadowPhaseLiveTailRightPhysicalPlay A
                strategy hwin tag state move tableMember localEnv) n)).length =
        profiledRawJointTargetRightPhysicalPrefixRecords A row
          (omegaPrefix
            (profiledRawJointHybridShadowPhaseLiveTailRightPhysicalPlay A
              strategy hwin tag state move tableMember localEnv) n) := by
  have hlength :
      (profiledRawJointTargetRightPhysicalPrefixRecords A row
        (omegaPrefix
          (profiledRawJointHybridShadowPhaseLiveTailRightPhysicalPlay A strategy
            hwin tag state move tableMember localEnv) n)).length = n := by
    simp [profiledRawJointTargetRightPhysicalPrefixRecords, omegaPrefix]
  exact ⟨hlength, by rw [hlength]; exact segment.records⟩

end ProfiledRawJointHybridShadowPhaseLiveTailRightLiteralPrefixAt

/-! ## Left local folds and literal segments -/

def ProfiledRawJointHybridShadowPhaseLiveTailLeftLocallyReachableAt
    (tag : Tag A strategy hwin) (state : TailState A strategy hwin tag)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (monitorState :
      (profiledRawJointHybridShadowPhaseLiveTailSuccessorLeftMonitor A strategy
        hwin (tag := tag) move false).State)
    (past : List (In₁ × In₂)) : Prop :=
  owner = (move.memberController A false).controlAt (senderWord past) ∧
    monitorState = narrowedControl
      (profiledRawJointHybridShadowPhaseLiveTailSuccessorLeftMonitor A strategy
        hwin (tag := tag) move false)
      (profiledRawJointHybridShadowPhaseLiveTailDecoratedLeftMemberController A
        strategy hwin state move false).labeledTree past

theorem
    profiledRawJointHybridShadowPhaseLiveTailLeftLocallyReachableAt_initial
    (tag : Tag A strategy hwin) (state : TailState A strategy hwin tag)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A) :
    ProfiledRawJointHybridShadowPhaseLiveTailLeftLocallyReachableAt A strategy
      hwin tag state move (move.memberController A false).initial
        (profiledRawJointHybridShadowPhaseLiveTailSuccessorLeftMonitor A strategy
          hwin (tag := tag) move false).initial [] :=
  ⟨rfl, rfl⟩

theorem
    ProfiledRawJointHybridShadowPhaseLiveTailLeftLocallyReachableAt.step
    {tag : Tag A strategy hwin} {state : TailState A strategy hwin tag}
    {move : ProfiledRawJointLeftPhysicalSiblingMove A}
    {owner : (move.memberController A false).Control}
    {monitorState :
      (profiledRawJointHybridShadowPhaseLiveTailSuccessorLeftMonitor A strategy
        hwin (tag := tag) move false).State}
    {past : List (In₁ × In₂)}
    (hreach :
      ProfiledRawJointHybridShadowPhaseLiveTailLeftLocallyReachableAt A strategy
        hwin tag state move owner monitorState past)
    (row : PairedEntryRow) (input : In₁ × In₂) :
    let result :=
      profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStepFor A strategy
        hwin tag state move owner row monitorState input
    ProfiledRawJointHybridShadowPhaseLiveTailLeftLocallyReachableAt A strategy
      hwin tag state move ((move.memberController A false).step owner input.2)
        (result.2.2.get (by rfl)).2.2.1 (past ++ [input]) := by
  rcases hreach with ⟨rfl, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [senderWord_append, TransitionRationalTree.controlAt_append]
    simp
  · rw [narrowedControl_append]
    rfl

theorem
    ProfiledRawJointHybridShadowPhaseLiveTailLeftLocallyReachableAt.output_eq_play
    {tag : Tag A strategy hwin} {state : TailState A strategy hwin tag}
    {move : ProfiledRawJointLeftPhysicalSiblingMove A}
    {owner : (move.memberController A false).Control}
    {monitorState :
      (profiledRawJointHybridShadowPhaseLiveTailSuccessorLeftMonitor A strategy
        hwin (tag := tag) move false).State}
    {past : List (In₁ × In₂)}
    (hreach :
      ProfiledRawJointHybridShadowPhaseLiveTailLeftLocallyReachableAt A strategy
        hwin tag state move owner monitorState past)
    (tableMember : Bool) (row : PairedEntryRow) (input : In₁ × In₂) :
    (profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStepFor A strategy
        hwin tag state move owner row monitorState input).1 =
      (profiledRawJointHybridShadowPhaseLiveTailLeftDecoratedPlay A strategy
        hwin tag state move tableMember (omegaOfList (past ++ [input]))
          past.length).2.1 := by
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
  cases tableMember <;>
    simp [profiledRawJointHybridShadowPhaseLiveTailLeftDecoratedPlay,
      profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStepFor,
      treePlay, narrowedInducedTree, blockLabelApply,
      TransitionRationalTree.labeledTree, branchNode_eq_omegaPrefix,
      hpast, env]
  all_goals rfl

structure ProfiledRawJointHybridShadowPhaseLiveTailLeftLiteralPrefixAt
    (tag : Tag A strategy hwin) (state : TailState A strategy hwin tag)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (tableMember : Bool) (row : PairedEntryRow)
    (localEnv : Nat → In₁ × In₂)
    (owner : (move.memberController A false).Control)
    (monitorState :
      (profiledRawJointHybridShadowPhaseLiveTailSuccessorLeftMonitor A strategy
        hwin (tag := tag) move false).State)
    (word : PhysicalWord (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂))
    (start n : Nat) : Prop where
  literal_reachable :
    ProfiledRawJointHybridShadowPhaseLiveTailLeftLocallyReachableAt A strategy
      hwin tag state move owner monitorState (omegaPrefix localEnv n)
  records :
    omegaPrefix (OmegaWord.drop word start) n =
      profiledRawJointTargetLeftPhysicalPrefixRecords A row
        (omegaPrefix
          (profiledRawJointHybridShadowPhaseLiveTailLeftPhysicalPlay A strategy
            hwin tag state move tableMember localEnv) n)

namespace ProfiledRawJointHybridShadowPhaseLiveTailLeftLiteralPrefixAt

theorem initial
    (tag : Tag A strategy hwin) (state : TailState A strategy hwin tag)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (tableMember : Bool) (row : PairedEntryRow)
    (localEnv : Nat → In₁ × In₂)
    (word : PhysicalWord (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)) (start : Nat) :
    ProfiledRawJointHybridShadowPhaseLiveTailLeftLiteralPrefixAt A strategy hwin
      tag state move tableMember row localEnv
        (move.memberController A false).initial
        (profiledRawJointHybridShadowPhaseLiveTailSuccessorLeftMonitor A strategy
          hwin (tag := tag) move false).initial word start 0 :=
  ⟨profiledRawJointHybridShadowPhaseLiveTailLeftLocallyReachableAt_initial A
      strategy hwin tag state move, rfl⟩

theorem step
    {tag : Tag A strategy hwin} {state : TailState A strategy hwin tag}
    {move : ProfiledRawJointLeftPhysicalSiblingMove A}
    {tableMember : Bool} {row : PairedEntryRow}
    {localEnv : Nat → In₁ × In₂}
    {owner : (move.memberController A false).Control}
    {monitorState :
      (profiledRawJointHybridShadowPhaseLiveTailSuccessorLeftMonitor A strategy
        hwin (tag := tag) move false).State}
    {word : PhysicalWord (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {start n : Nat}
    (segment :
      ProfiledRawJointHybridShadowPhaseLiveTailLeftLiteralPrefixAt A strategy
        hwin tag state move tableMember row localEnv owner monitorState word
          start n)
    (hrecord : word (start + n) =
      pairedLeftRecordForRow row
        (profiledRawJointTargetLeftPhysicalLetter A
          (profiledRawJointHybridShadowPhaseLiveTailLeftPhysicalPlay A strategy
            hwin tag state move tableMember localEnv n))) :
    let result :=
      profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStepFor A strategy
        hwin tag state move owner row monitorState (localEnv n)
    ProfiledRawJointHybridShadowPhaseLiveTailLeftLiteralPrefixAt A strategy hwin
      tag state move tableMember row localEnv
        ((move.memberController A false).step owner (localEnv n).2)
        (result.2.2.get (by rfl)).2.2.1 word start (n + 1) := by
  dsimp only
  constructor
  · simpa only [omegaPrefix_succ] using
      segment.literal_reachable.step A strategy hwin row (localEnv n)
  · rw [omegaPrefix_succ, omegaPrefix_succ, segment.records]
    simp only [OmegaWord.drop]
    rw [hrecord]
    simp [profiledRawJointTargetLeftPhysicalPrefixRecords]

theorem cutPrefix
    {tag : Tag A strategy hwin} {state : TailState A strategy hwin tag}
    {move : ProfiledRawJointLeftPhysicalSiblingMove A}
    {tableMember : Bool} {row : PairedEntryRow}
    {localEnv : Nat → In₁ × In₂}
    {owner : (move.memberController A false).Control}
    {monitorState :
      (profiledRawJointHybridShadowPhaseLiveTailSuccessorLeftMonitor A strategy
        hwin (tag := tag) move false).State}
    {word : PhysicalWord (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {start n : Nat}
    (segment :
      ProfiledRawJointHybridShadowPhaseLiveTailLeftLiteralPrefixAt A strategy
        hwin tag state move tableMember row localEnv owner monitorState word
          start n) :
    (profiledRawJointTargetLeftPhysicalPrefixRecords A row
        (omegaPrefix
          (profiledRawJointHybridShadowPhaseLiveTailLeftPhysicalPlay A strategy
            hwin tag state move tableMember localEnv) n)).length = n ∧
      omegaPrefix (OmegaWord.drop word start)
          (profiledRawJointTargetLeftPhysicalPrefixRecords A row
            (omegaPrefix
              (profiledRawJointHybridShadowPhaseLiveTailLeftPhysicalPlay A
                strategy hwin tag state move tableMember localEnv) n)).length =
        profiledRawJointTargetLeftPhysicalPrefixRecords A row
          (omegaPrefix
            (profiledRawJointHybridShadowPhaseLiveTailLeftPhysicalPlay A
              strategy hwin tag state move tableMember localEnv) n) := by
  have hlength :
      (profiledRawJointTargetLeftPhysicalPrefixRecords A row
        (omegaPrefix
          (profiledRawJointHybridShadowPhaseLiveTailLeftPhysicalPlay A strategy
            hwin tag state move tableMember localEnv) n)).length = n := by
    simp [profiledRawJointTargetLeftPhysicalPrefixRecords, omegaPrefix]
  exact ⟨hlength, by rw [hlength]; exact segment.records⟩

end ProfiledRawJointHybridShadowPhaseLiveTailLeftLiteralPrefixAt

end


end DetParityAutomaton

end DistributedSynthesis
