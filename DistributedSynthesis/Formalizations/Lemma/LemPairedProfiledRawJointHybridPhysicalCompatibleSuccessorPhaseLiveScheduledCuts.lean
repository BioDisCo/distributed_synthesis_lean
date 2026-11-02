/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorPhaseLivePhysicalSegment

/-!
# Operational cuts of the compatible successor phase-live trace

The physical-segment invariant retains the installation time of every live
table.  This module begins the conversion to operational-close packets.  It
first exposes the graph orientation of every literal prefix record and then
shows that a selected strict table at a successor cut was installed exactly
at that cut.  The latter rules out an older installation with the preceding
closing round, whose graph is necessarily different from the new strict
block.
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

private abbrev PhysicalWord :=
  OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂)

private abbrev RightOutput
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleSuccessorRightReceiverOutput A
    strategy hwin initial

private abbrev LeftOutput
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleSuccessorLeftReceiverOutput A
    strategy hwin initial

private abbrev OnePending
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  ProfiledRawJointHybridPhysicalCompatiblePhaseLiveOnePending A strategy hwin
    policy

private abbrev TwoPending
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTwoPending A strategy hwin
    policy

private abbrev OneControl
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (ProfiledRawJointHybridPhysicalCompatiblePhaseLiveOneShared A strategy hwin
      policy) PUnit PUnit

private abbrev TwoControl
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTwoShared A strategy hwin
      policy) PUnit PUnit

/-! ## Graph projections of literal prefixes -/

theorem
    ProfiledRawJointHybridPhysicalCompatibleRightLiteralPrefixAt.graph_eq_right
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {state : CompatibleState A strategy hwin initial}
    {move : ProfiledRawJointRightPhysicalSiblingMove A}
    {tableMember : Bool} {row : PairedEntryRow}
    {localEnv : Nat → In₂ × In₁}
    {owner : (move.memberController A false).Control}
    {monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A
        strategy hwin (initial := initial) move false).State}
    {word : PhysicalWord (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {start n : Nat}
    (segment :
      ProfiledRawJointHybridPhysicalCompatibleRightLiteralPrefixAt A strategy
        hwin policy state move tableMember row localEnv owner monitorState word
          start n)
    (j : Nat) (hj : j < n) :
    (word (start + j)).graph = .right := by
  have hrecord :
      word (start + j) =
        pairedRightRecordForRow row
          (profiledRawJointTargetRightPhysicalLetter A
            (profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A
              strategy hwin policy state move tableMember localEnv j)) := by
    have h := congrArg (fun records ↦ records[j]?) segment.records
    simpa [omegaPrefix,
      profiledRawJointTargetRightPhysicalPrefixRecords, hj] using h
  cases row <;>
    simpa [pairedRightRecordForRow, rightRoundRecord] using
      congrArg RoundRecord.graph hrecord

theorem
    ProfiledRawJointHybridPhysicalCompatibleLeftLiteralPrefixAt.graph_eq_left
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {state : CompatibleState A strategy hwin initial}
    {move : ProfiledRawJointLeftPhysicalSiblingMove A}
    {tableMember : Bool} {row : PairedEntryRow}
    {localEnv : Nat → In₁ × In₂}
    {owner : (move.memberController A false).Control}
    {monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A
        strategy hwin (initial := initial) move false).State}
    {word : PhysicalWord (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {start n : Nat}
    (segment :
      ProfiledRawJointHybridPhysicalCompatibleLeftLiteralPrefixAt A strategy
        hwin policy state move tableMember row localEnv owner monitorState word
          start n)
    (j : Nat) (hj : j < n) :
    (word (start + j)).graph = .left := by
  have hrecord :
      word (start + j) =
        pairedLeftRecordForRow row
          (profiledRawJointTargetLeftPhysicalLetter A
            (profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A
              strategy hwin policy state move tableMember localEnv j)) := by
    have h := congrArg (fun records ↦ records[j]?) segment.records
    simpa [omegaPrefix,
      profiledRawJointTargetLeftPhysicalPrefixRecords, hj] using h
  cases row <;>
    simpa [pairedLeftRecordForRow, leftRoundRecord] using
      congrArg RoundRecord.graph hrecord

/-! ## The preceding close differs from a new strict block -/

theorem OperationalCloseCutPackage.previous_closing_graph_ne_current
    {graphs : Nat → Graph} (cuts : OperationalCloseCutPackage graphs) (k : Nat)
    (hcurrent : graphs (cuts.cuts (k + 1)) ≠ .both) :
    graphs (cuts.cuts (k + 1) - 1) ≠ graphs (cuts.cuts (k + 1)) := by
  intro heq
  rw [cuts.closing_graph_eq k] at heq
  by_cases hprevious : graphs (cuts.cuts k) = .both
  · exact hcurrent (heq.symm.trans hprevious)
  · exact cuts.maximal_of_strict k hprevious heq.symm

/-! ## Exact installation time at successor cuts -/

theorem
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightPhysicalSegmentAt.start_eq_successorCut
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {env : EnvironmentSequence In₁ In₂}
    {word : PhysicalWord (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {n : Nat} {tableMember : Bool}
    {owner : ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightOwner A
      strategy hwin policy}
    {receiver :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiver A
        strategy hwin (initial := initial)}
    (segment :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightPhysicalSegmentAt
        A strategy hwin policy env word n tableMember owner receiver)
    (schedule : OperationalCloseMemberSchedule (fun j ↦ (word j).graph))
    (k : Nat) (hn : n = schedule.cutPackage.cuts (k + 1))
    (hgraph : (word n).graph = .right) :
    ∃ (state : CompatibleState A strategy hwin initial)
        (move : ProfiledRawJointRightPhysicalSiblingMove A)
        (ownerControl : (move.memberController A false).Control)
        (row : PairedEntryRow)
        (monitorState :
          (profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A
            strategy hwin (initial := initial) move false).State)
        (staged : Option
          (ProfiledRawJointHybridPhysicalCompatibleSuccessorRightReceiverOutput
            A strategy hwin initial)),
      owner = ⟨state, .inr ⟨move, ownerControl⟩⟩ ∧
        receiver = ⟨state, some ⟨move, row, monitorState, staged⟩⟩ ∧
        ProfiledRawJointHybridPhysicalCompatibleRightLiteralPrefixAt A
          strategy hwin policy state move tableMember row
            (fun j ↦ ((env (n + j)).inputTwo, (env (n + j)).inputOne))
            ownerControl monitorState word n 0 := by
  rcases segment with
    ⟨start, state, move, ownerControl, row, monitorState, staged,
      hstart, howner, hreceiver, hliteral⟩
  have hstartEq : start = n := by
    by_contra hne
    have hlt : start < n := lt_of_le_of_ne hstart hne
    have hj : n - 1 - start < n - start := by omega
    have hindex : start + (n - 1 - start) = n - 1 := by omega
    have hpreviousRight :=
      hliteral.graph_eq_right A strategy hwin (n - 1 - start) hj
    rw [hindex] at hpreviousRight
    have hpreviousNe :=
      DetParityAutomaton.OperationalCloseCutPackage.previous_closing_graph_ne_current
        schedule.cutPackage k (by
        rw [← hn]
        simp [hgraph])
    rw [← hn] at hpreviousNe
    exact hpreviousNe (hpreviousRight.trans hgraph.symm)
  subst start
  refine ⟨state, move, ownerControl, row, monitorState, staged,
    howner, hreceiver, ?_⟩
  simpa using hliteral

theorem
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftPhysicalSegmentAt.start_eq_successorCut
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {env : EnvironmentSequence In₁ In₂}
    {word : PhysicalWord (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {n : Nat} {tableMember : Bool}
    {owner : ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftOwner A
      strategy hwin policy}
    {receiver :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiver A
        strategy hwin (initial := initial)}
    (segment :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftPhysicalSegmentAt A
        strategy hwin policy env word n tableMember owner receiver)
    (schedule : OperationalCloseMemberSchedule (fun j ↦ (word j).graph))
    (k : Nat) (hn : n = schedule.cutPackage.cuts (k + 1))
    (hgraph : (word n).graph = .left) :
    ∃ (state : CompatibleState A strategy hwin initial)
        (move : ProfiledRawJointLeftPhysicalSiblingMove A)
        (ownerControl : (move.memberController A false).Control)
        (row : PairedEntryRow)
        (monitorState :
          (profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A
            strategy hwin (initial := initial) move false).State)
        (staged : Option
          (ProfiledRawJointHybridPhysicalCompatibleSuccessorLeftReceiverOutput
            A strategy hwin initial)),
      owner = ⟨state, .inr ⟨move, ownerControl⟩⟩ ∧
        receiver = ⟨state, some ⟨move, row, monitorState, staged⟩⟩ ∧
        ProfiledRawJointHybridPhysicalCompatibleLeftLiteralPrefixAt A strategy
          hwin policy state move tableMember row
            (fun j ↦ ((env (n + j)).inputOne, (env (n + j)).inputTwo))
            ownerControl monitorState word n 0 := by
  rcases segment with
    ⟨start, state, move, ownerControl, row, monitorState, staged,
      hstart, howner, hreceiver, hliteral⟩
  have hstartEq : start = n := by
    by_contra hne
    have hlt : start < n := lt_of_le_of_ne hstart hne
    have hj : n - 1 - start < n - start := by omega
    have hindex : start + (n - 1 - start) = n - 1 := by omega
    have hpreviousLeft :=
      hliteral.graph_eq_left A strategy hwin (n - 1 - start) hj
    rw [hindex] at hpreviousLeft
    have hpreviousNe :=
      DetParityAutomaton.OperationalCloseCutPackage.previous_closing_graph_ne_current
        schedule.cutPackage k (by
        rw [← hn]
        simp [hgraph])
    rw [← hn] at hpreviousNe
    exact hpreviousNe (hpreviousLeft.trans hgraph.symm)
  subst start
  refine ⟨state, move, ownerControl, row, monitorState, staged,
    howner, hreceiver, ?_⟩
  simpa using hliteral

/-! ## Anchored epochs -/

/-- The anchored form of a right physical epoch exposes its installation cut.
Unlike the unanchored all-time invariant, this form can be folded across an
entire homogeneous operational block without losing the start index hidden by
an existential. -/
def ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightAnchoredPhysicalSegmentAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (env : EnvironmentSequence In₁ In₂)
    (word : PhysicalWord (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂))
    (start n : Nat) (tableMember : Bool)
    (owner : ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightOwner A
      strategy hwin policy)
    (receiver :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiver A
        strategy hwin (initial := initial)) : Prop :=
  start ≤ n ∧
    ∃ (state : CompatibleState A strategy hwin initial)
        (move : ProfiledRawJointRightPhysicalSiblingMove A)
        (ownerControl : (move.memberController A false).Control)
        (row : PairedEntryRow)
        (monitorState :
          (profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A
            strategy hwin (initial := initial) move false).State)
        (staged : Option (RightOutput A strategy hwin initial)),
      owner = ⟨state, .inr ⟨move, ownerControl⟩⟩ ∧
        receiver = ⟨state, some ⟨move, row, monitorState, staged⟩⟩ ∧
        ProfiledRawJointHybridPhysicalCompatibleRightLiteralPrefixAt A
          strategy hwin policy state move tableMember row
            (fun j ↦ ((env (start + j)).inputTwo,
              (env (start + j)).inputOne))
            ownerControl monitorState word start (n - start)

/-- The successor-cut theorem promotes the selected unanchored epoch to an
epoch anchored at that exact cut. -/
theorem
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightPhysicalSegmentAt.anchoredAt_successorCut
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {env : EnvironmentSequence In₁ In₂}
    {word : PhysicalWord (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {n : Nat} {tableMember : Bool}
    {owner : ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightOwner A
      strategy hwin policy}
    {receiver :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiver A
        strategy hwin (initial := initial)}
    (segment :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightPhysicalSegmentAt
        A strategy hwin policy env word n tableMember owner receiver)
    (schedule : OperationalCloseMemberSchedule (fun j ↦ (word j).graph))
    (k : Nat) (hn : n = schedule.cutPackage.cuts (k + 1))
    (hgraph : (word n).graph = .right) :
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightAnchoredPhysicalSegmentAt
      A strategy hwin policy env word n n tableMember owner receiver := by
  refine ⟨le_rfl, ?_⟩
  simpa using segment.start_eq_successorCut A strategy hwin schedule k hn hgraph

/-- A strict-right semantic round extends an anchored epoch while retaining
the same installation cut and the same table identity. -/
theorem
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightAnchoredPhysicalSegmentAt.stepSemantic
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (hinitial :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂) (start n : Nat)
    (one : OnePending A strategy hwin policy)
    (two : TwoPending A strategy hwin policy)
    (hinvariant :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy one two)
    (hpair :
      ((.inl one : OneControl A strategy hwin policy),
          (.inl two : TwoControl A strategy hwin policy)) =
        profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env n)
    (hgraph : (env n).graph = .right)
    (tableMember : Bool)
    (segment :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightAnchoredPhysicalSegmentAt
        A strategy hwin policy env
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
            strategy hwin policy initialOne initialTwo fallbackLeft
              fallbackRight env)
          start n tableMember one.2.1.baseShared
            (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverForRecvTwo
              A strategy hwin policy two one)) :
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightAnchoredPhysicalSegmentAt
      A strategy hwin policy env
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env)
        start (n + 1) tableMember
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightOwnerStep A
          strategy hwin policy one.1 one.2.1.baseShared
            (env n).inputOne).1
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvTwoRight A
          strategy hwin policy fallbackRight two one
            ((env n).inputTwo, (env n).inputOne)).2 := by
  rcases segment with
    ⟨hstart, state, move, ownerControl, row, monitorState, staged,
      howner, hreceiver, hliteral⟩
  let localEnv : Nat → In₂ × In₁ :=
    fun j ↦ ((env (start + j)).inputTwo, (env (start + j)).inputOne)
  have hindex : start + (n - start) = n := Nat.add_sub_of_le hstart
  have hinput : localEnv (n - start) =
      ((env n).inputTwo, (env n).inputOne) := by
    simp only [localEnv, hindex]
  have hsemantic :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord_strictRight_pending
      A strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
        hinitial env n one two hinvariant hpair hgraph
  have hrow :
      profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverRow A
          strategy hwin
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverForRecvTwo
            A strategy hwin policy two one) = row := by
    rw [hreceiver]
    rfl
  rw [hrow] at hsemantic
  have hplay :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveRightRecord_eq_play A
      strategy hwin policy fallbackRight state move ownerControl row
        monitorState staged (omegaPrefix localEnv (n - start))
        hliteral.literal_reachable tableMember one.1 localEnv (n - start) rfl
  rw [hinput] at hplay
  have hplay' := hplay
  rw [← howner, ← hreceiver] at hplay'
  have hrecord :
      profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A strategy
          hwin policy initialOne initialTwo fallbackLeft fallbackRight env
          (start + (n - start)) =
        pairedRightRecordForRow row
          (profiledRawJointTargetRightPhysicalLetter A
            (profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A
              strategy hwin policy state move tableMember localEnv
                (n - start))) := by
    rw [hindex]
    exact hsemantic.trans (by simpa using hplay')
  let result :=
    profiledRawJointHybridPhysicalCompatibleRightReceiverStepFor A strategy
      hwin policy state move ownerControl row monitorState
        ((env n).inputTwo, (env n).inputOne)
  have hliteralNext := hliteral.step A strategy hwin hrecord
  refine ⟨Nat.le_trans hstart (by omega), state, move,
    (move.memberController A false).step ownerControl (env n).inputOne,
    row, result.2.2.2.1, some result.1, ?_, ?_, ?_⟩
  · rw [howner]
    simp [profiledRawJointHybridPhysicalCompatiblePhaseLiveRightOwnerStep,
      profiledRawJointHybridPhysicalCompatibleRightSharedStep]
    exact
      (profiledRawJointRightPhysicalSiblingDeferredStep_laws A move).state_eq
        one.1 false ownerControl (env n).inputOne
  · simp only
      [profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvTwoRight]
    rw [howner, hreceiver]
    simp [
      profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverStep,
      result]
    rfl
  · have hlength : n + 1 - start = (n - start) + 1 := by omega
    rw [hindex] at hliteralNext
    rw [hlength]
    exact hliteralNext

/-- Left-oriented anchored epoch. -/
def ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftAnchoredPhysicalSegmentAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (env : EnvironmentSequence In₁ In₂)
    (word : PhysicalWord (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂))
    (start n : Nat) (tableMember : Bool)
    (owner : ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftOwner A
      strategy hwin policy)
    (receiver :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiver A
        strategy hwin (initial := initial)) : Prop :=
  start ≤ n ∧
    ∃ (state : CompatibleState A strategy hwin initial)
        (move : ProfiledRawJointLeftPhysicalSiblingMove A)
        (ownerControl : (move.memberController A false).Control)
        (row : PairedEntryRow)
        (monitorState :
          (profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A
            strategy hwin (initial := initial) move false).State)
        (staged : Option (LeftOutput A strategy hwin initial)),
      owner = ⟨state, .inr ⟨move, ownerControl⟩⟩ ∧
        receiver = ⟨state, some ⟨move, row, monitorState, staged⟩⟩ ∧
        ProfiledRawJointHybridPhysicalCompatibleLeftLiteralPrefixAt A strategy
          hwin policy state move tableMember row
            (fun j ↦ ((env (start + j)).inputOne,
              (env (start + j)).inputTwo))
            ownerControl monitorState word start (n - start)

theorem
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftPhysicalSegmentAt.anchoredAt_successorCut
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {env : EnvironmentSequence In₁ In₂}
    {word : PhysicalWord (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {n : Nat} {tableMember : Bool}
    {owner : ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftOwner A
      strategy hwin policy}
    {receiver :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiver A
        strategy hwin (initial := initial)}
    (segment :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftPhysicalSegmentAt A
        strategy hwin policy env word n tableMember owner receiver)
    (schedule : OperationalCloseMemberSchedule (fun j ↦ (word j).graph))
    (k : Nat) (hn : n = schedule.cutPackage.cuts (k + 1))
    (hgraph : (word n).graph = .left) :
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftAnchoredPhysicalSegmentAt
      A strategy hwin policy env word n n tableMember owner receiver := by
  refine ⟨le_rfl, ?_⟩
  simpa using segment.start_eq_successorCut A strategy hwin schedule k hn hgraph

/-- Left strict-round mirror of anchored epoch preservation. -/
theorem
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftAnchoredPhysicalSegmentAt.stepSemantic
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (hinitial :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂) (start n : Nat)
    (one : OnePending A strategy hwin policy)
    (two : TwoPending A strategy hwin policy)
    (hinvariant :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy one two)
    (hpair :
      ((.inl one : OneControl A strategy hwin policy),
          (.inl two : TwoControl A strategy hwin policy)) =
        profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env n)
    (hgraph : (env n).graph = .left)
    (tableMember : Bool)
    (segment :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftAnchoredPhysicalSegmentAt
        A strategy hwin policy env
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
            strategy hwin policy initialOne initialTwo fallbackLeft
              fallbackRight env)
          start n tableMember two.2.1.baseShared
            (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverForRecvOne
              A strategy hwin policy one two)) :
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftAnchoredPhysicalSegmentAt
      A strategy hwin policy env
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env)
        start (n + 1) tableMember
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftOwnerStep A
          strategy hwin policy two.1 two.2.1.baseShared
            (env n).inputTwo).1
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvOneLeft A
          strategy hwin policy fallbackLeft one two
            ((env n).inputOne, (env n).inputTwo)).2 := by
  rcases segment with
    ⟨hstart, state, move, ownerControl, row, monitorState, staged,
      howner, hreceiver, hliteral⟩
  let localEnv : Nat → In₁ × In₂ :=
    fun j ↦ ((env (start + j)).inputOne, (env (start + j)).inputTwo)
  have hindex : start + (n - start) = n := Nat.add_sub_of_le hstart
  have hinput : localEnv (n - start) =
      ((env n).inputOne, (env n).inputTwo) := by
    simp only [localEnv, hindex]
  have hsemantic :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord_strictLeft_pending
      A strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
        hinitial env n one two hinvariant hpair hgraph
  have hrow :
      profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverRow A
          strategy hwin
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverForRecvOne
            A strategy hwin policy one two) = row := by
    rw [hreceiver]
    rfl
  rw [hrow] at hsemantic
  have hplay :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftRecord_eq_play A
      strategy hwin policy fallbackLeft state move ownerControl row monitorState
        staged (omegaPrefix localEnv (n - start))
        hliteral.literal_reachable tableMember two.1 localEnv (n - start) rfl
  rw [hinput] at hplay
  have hplay' := hplay
  rw [← howner, ← hreceiver] at hplay'
  have hrecord :
      profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A strategy
          hwin policy initialOne initialTwo fallbackLeft fallbackRight env
          (start + (n - start)) =
        pairedLeftRecordForRow row
          (profiledRawJointTargetLeftPhysicalLetter A
            (profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A
              strategy hwin policy state move tableMember localEnv
                (n - start))) := by
    rw [hindex]
    exact hsemantic.trans (by simpa using hplay')
  let result :=
    profiledRawJointHybridPhysicalCompatibleLeftReceiverStepFor A strategy hwin
      policy state move ownerControl row monitorState
        ((env n).inputOne, (env n).inputTwo)
  have hliteralNext := hliteral.step A strategy hwin hrecord
  refine ⟨Nat.le_trans hstart (by omega), state, move,
    (move.memberController A false).step ownerControl (env n).inputTwo,
    row, result.2.2.2.1, some result.1, ?_, ?_, ?_⟩
  · rw [howner]
    simp [profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftOwnerStep,
      profiledRawJointHybridPhysicalCompatibleLeftSharedStep]
    exact
      (profiledRawJointLeftPhysicalSiblingDeferredStep_laws A move).state_eq
        two.1 false ownerControl (env n).inputTwo
  · simp only
      [profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvOneLeft]
    rw [howner, hreceiver]
    simp [
      profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverStep,
      result]
    rfl
  · have hlength : n + 1 - start = (n - start) + 1 := by omega
    rw [hindex] at hliteralNext
    rw [hlength]
    exact hliteralNext

/-! ## The record at the open-block boundary -/

/-- An anchored right epoch identifies the actual record of its next strict
round.  This is the closing record when the epoch has open length. -/
theorem
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightAnchoredPhysicalSegmentAt.currentRecord_eq
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (hinitial :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂) (start n : Nat)
    (one : OnePending A strategy hwin policy)
    (two : TwoPending A strategy hwin policy)
    (hinvariant :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy one two)
    (hpair :
      ((.inl one : OneControl A strategy hwin policy),
          (.inl two : TwoControl A strategy hwin policy)) =
        profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env n)
    (hgraph : (env n).graph = .right)
    (tableMember : Bool)
    (segment :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightAnchoredPhysicalSegmentAt
        A strategy hwin policy env
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
            strategy hwin policy initialOne initialTwo fallbackLeft
              fallbackRight env)
          start n tableMember one.2.1.baseShared
            (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverForRecvTwo
              A strategy hwin policy two one)) :
    ∃ (state : CompatibleState A strategy hwin initial)
        (move : ProfiledRawJointRightPhysicalSiblingMove A)
        (ownerControl : (move.memberController A false).Control)
        (row : PairedEntryRow)
        (monitorState :
          (profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A
            strategy hwin (initial := initial) move false).State)
        (staged : Option (RightOutput A strategy hwin initial)),
      one.2.1.baseShared = ⟨state, .inr ⟨move, ownerControl⟩⟩ ∧
        profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverForRecvTwo
            A strategy hwin policy two one =
          ⟨state, some ⟨move, row, monitorState, staged⟩⟩ ∧
        ProfiledRawJointHybridPhysicalCompatibleRightLiteralPrefixAt A strategy
            hwin policy state move tableMember row
              (fun j ↦ ((env (start + j)).inputTwo,
                (env (start + j)).inputOne))
              ownerControl monitorState
              (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
                strategy hwin policy initialOne initialTwo fallbackLeft
                  fallbackRight env)
              start (n - start) ∧
        profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
            strategy hwin policy initialOne initialTwo fallbackLeft
              fallbackRight env n =
          pairedRightRecordForRow row
            (profiledRawJointTargetRightPhysicalLetter A
              (profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A
                strategy hwin policy state move tableMember
                  (fun j ↦ ((env (start + j)).inputTwo,
                    (env (start + j)).inputOne))
                  (n - start))) := by
  rcases segment with
    ⟨hstart, state, move, ownerControl, row, monitorState, staged,
      howner, hreceiver, hliteral⟩
  let localEnv : Nat → In₂ × In₁ :=
    fun j ↦ ((env (start + j)).inputTwo, (env (start + j)).inputOne)
  have hindex : start + (n - start) = n := Nat.add_sub_of_le hstart
  have hinput : localEnv (n - start) =
      ((env n).inputTwo, (env n).inputOne) := by
    simp only [localEnv, hindex]
  have hsemantic :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord_strictRight_pending
      A strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
        hinitial env n one two hinvariant hpair hgraph
  have hrow :
      profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverRow A
          strategy hwin
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverForRecvTwo
            A strategy hwin policy two one) = row := by
    rw [hreceiver]
    rfl
  rw [hrow] at hsemantic
  have hplay :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveRightRecord_eq_play A
      strategy hwin policy fallbackRight state move ownerControl row
        monitorState staged (omegaPrefix localEnv (n - start))
        hliteral.literal_reachable tableMember one.1 localEnv (n - start) rfl
  rw [hinput] at hplay
  have hplay' := hplay
  rw [← howner, ← hreceiver] at hplay'
  refine ⟨state, move, ownerControl, row, monitorState, staged, howner,
    hreceiver, by simpa [localEnv] using hliteral, ?_⟩
  exact hsemantic.trans (by simpa [localEnv] using hplay')

/-- Left current-record mirror. -/
theorem
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftAnchoredPhysicalSegmentAt.currentRecord_eq
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (hinitial :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂) (start n : Nat)
    (one : OnePending A strategy hwin policy)
    (two : TwoPending A strategy hwin policy)
    (hinvariant :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy one two)
    (hpair :
      ((.inl one : OneControl A strategy hwin policy),
          (.inl two : TwoControl A strategy hwin policy)) =
        profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env n)
    (hgraph : (env n).graph = .left)
    (tableMember : Bool)
    (segment :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftAnchoredPhysicalSegmentAt
        A strategy hwin policy env
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
            strategy hwin policy initialOne initialTwo fallbackLeft
              fallbackRight env)
          start n tableMember two.2.1.baseShared
            (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverForRecvOne
              A strategy hwin policy one two)) :
    ∃ (state : CompatibleState A strategy hwin initial)
        (move : ProfiledRawJointLeftPhysicalSiblingMove A)
        (ownerControl : (move.memberController A false).Control)
        (row : PairedEntryRow)
        (monitorState :
          (profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A
            strategy hwin (initial := initial) move false).State)
        (staged : Option (LeftOutput A strategy hwin initial)),
      two.2.1.baseShared = ⟨state, .inr ⟨move, ownerControl⟩⟩ ∧
        profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverForRecvOne
            A strategy hwin policy one two =
          ⟨state, some ⟨move, row, monitorState, staged⟩⟩ ∧
        ProfiledRawJointHybridPhysicalCompatibleLeftLiteralPrefixAt A strategy
            hwin policy state move tableMember row
              (fun j ↦ ((env (start + j)).inputOne,
                (env (start + j)).inputTwo))
              ownerControl monitorState
              (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
                strategy hwin policy initialOne initialTwo fallbackLeft
                  fallbackRight env)
              start (n - start) ∧
        profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
            strategy hwin policy initialOne initialTwo fallbackLeft
              fallbackRight env n =
          pairedLeftRecordForRow row
            (profiledRawJointTargetLeftPhysicalLetter A
              (profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A
                strategy hwin policy state move tableMember
                  (fun j ↦ ((env (start + j)).inputOne,
                    (env (start + j)).inputTwo))
                  (n - start))) := by
  rcases segment with
    ⟨hstart, state, move, ownerControl, row, monitorState, staged,
      howner, hreceiver, hliteral⟩
  let localEnv : Nat → In₁ × In₂ :=
    fun j ↦ ((env (start + j)).inputOne, (env (start + j)).inputTwo)
  have hindex : start + (n - start) = n := Nat.add_sub_of_le hstart
  have hinput : localEnv (n - start) =
      ((env n).inputOne, (env n).inputTwo) := by
    simp only [localEnv, hindex]
  have hsemantic :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord_strictLeft_pending
      A strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
        hinitial env n one two hinvariant hpair hgraph
  have hrow :
      profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverRow A
          strategy hwin
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverForRecvOne
            A strategy hwin policy one two) = row := by
    rw [hreceiver]
    rfl
  rw [hrow] at hsemantic
  have hplay :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftRecord_eq_play A
      strategy hwin policy fallbackLeft state move ownerControl row monitorState
        staged (omegaPrefix localEnv (n - start))
        hliteral.literal_reachable tableMember two.1 localEnv (n - start) rfl
  rw [hinput] at hplay
  have hplay' := hplay
  rw [← howner, ← hreceiver] at hplay'
  refine ⟨state, move, ownerControl, row, monitorState, staged, howner,
    hreceiver, by simpa [localEnv] using hliteral, ?_⟩
  exact hsemantic.trans (by simpa [localEnv] using hplay')

/-! ## Homogeneous strict blocks -/

/-- Fold one anchored right table through an arbitrary finite homogeneous
strict-right interval of the semantic trace. -/
theorem
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightAnchoredPhysicalSegmentAt.homogeneous
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (hinitial :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂) (anchor n length : Nat)
    (one : OnePending A strategy hwin policy)
    (two : TwoPending A strategy hwin policy)
    (hinvariant :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy one two)
    (hpair :
      ((.inl one : OneControl A strategy hwin policy),
          (.inl two : TwoControl A strategy hwin policy)) =
        profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env n)
    (tableMember : Bool)
    (segment :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightAnchoredPhysicalSegmentAt
        A strategy hwin policy env
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
            strategy hwin policy initialOne initialTwo fallbackLeft
              fallbackRight env)
          anchor n tableMember one.2.1.baseShared
            (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverForRecvTwo
              A strategy hwin policy two one))
    (hgraph : ∀ j, j < length → (env (n + j)).graph = .right) :
    ∃ (oneEnd : OnePending A strategy hwin policy)
        (twoEnd : TwoPending A strategy hwin policy),
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
          strategy hwin policy oneEnd twoEnd ∧
        ((.inl oneEnd : OneControl A strategy hwin policy),
            (.inl twoEnd : TwoControl A strategy hwin policy)) =
          profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace A
            strategy hwin policy initialOne initialTwo fallbackLeft
              fallbackRight env (n + length) ∧
        ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightAnchoredPhysicalSegmentAt
          A strategy hwin policy env
            (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
              strategy hwin policy initialOne initialTwo fallbackLeft
                fallbackRight env)
            anchor (n + length) tableMember oneEnd.2.1.baseShared
              (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverForRecvTwo
                A strategy hwin policy twoEnd oneEnd) := by
  induction length generalizing n one two with
  | zero =>
      exact ⟨one, two, hinvariant, by simpa using hpair, by simpa using segment⟩
  | succ length ih =>
      have hgraphNow : (env n).graph = .right := by
        simpa using hgraph 0 (Nat.zero_lt_succ length)
      let oneNext : OnePending A strategy hwin policy :=
        (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveOnePendingStep A
            strategy hwin policy) one (env n).inputOne).1
      let fresh :=
        profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair.{u, v, x,
          y, s, max u v x y s, max u v x y s, max u v x y s,
          max u v x y s} A strategy hwin policy fallbackLeft fallbackRight one
            two ((env n).inputOne, (env n).inputTwo)
      let twoNext : TwoPending A strategy hwin policy := fresh.1.2.openControl
      have hinvariantNext := hinvariant.strictRight A strategy hwin
        fallbackLeft fallbackRight ((env n).inputOne, (env n).inputTwo)
      have hsegmentNext := segment.stepSemantic A strategy hwin policy
        initialOne initialTwo fallbackLeft fallbackRight hinitial env anchor n
          one two hinvariant hpair hgraphNow tableMember
      have hpairNext :
          ((.inl oneNext : OneControl A strategy hwin policy),
              (.inl twoNext : TwoControl A strategy hwin policy)) =
            profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace A
              strategy hwin policy initialOne initialTwo fallbackLeft
                fallbackRight env (n + 1) := by
        simpa
          [profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace,
            FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
            hgraphNow, oneNext, twoNext, fresh]
          using congrArg
            (fun controls : OneControl A strategy hwin policy ×
                TwoControl A strategy hwin policy ↦
              ((profiledRawJointHybridPhysicalCompatiblePhaseLiveNoRecvOne A
                  strategy hwin policy controls.1 (env n).inputOne).1,
                (profiledRawJointHybridPhysicalCompatiblePhaseLiveOpenRecvTwo
                  A strategy hwin policy initialTwo fallbackLeft fallbackRight
                    controls.2 (env n).inputTwo controls.1
                      (env n).inputOne).1))
            hpair
      have htail : ∀ j, j < length →
          (env ((n + 1) + j)).graph = .right := by
        intro j hj
        have h := hgraph (j + 1) (Nat.succ_lt_succ hj)
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      have hrest := ih (n := n + 1) oneNext twoNext hinvariantNext hpairNext
        hsegmentNext htail
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrest

/-- Fold one anchored left table through a homogeneous strict-left interval. -/
theorem
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftAnchoredPhysicalSegmentAt.homogeneous
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (hinitial :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂) (anchor n length : Nat)
    (one : OnePending A strategy hwin policy)
    (two : TwoPending A strategy hwin policy)
    (hinvariant :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy one two)
    (hpair :
      ((.inl one : OneControl A strategy hwin policy),
          (.inl two : TwoControl A strategy hwin policy)) =
        profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env n)
    (tableMember : Bool)
    (segment :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftAnchoredPhysicalSegmentAt
        A strategy hwin policy env
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
            strategy hwin policy initialOne initialTwo fallbackLeft
              fallbackRight env)
          anchor n tableMember two.2.1.baseShared
            (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverForRecvOne
              A strategy hwin policy one two))
    (hgraph : ∀ j, j < length → (env (n + j)).graph = .left) :
    ∃ (oneEnd : OnePending A strategy hwin policy)
        (twoEnd : TwoPending A strategy hwin policy),
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
          strategy hwin policy oneEnd twoEnd ∧
        ((.inl oneEnd : OneControl A strategy hwin policy),
            (.inl twoEnd : TwoControl A strategy hwin policy)) =
          profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace A
            strategy hwin policy initialOne initialTwo fallbackLeft
              fallbackRight env (n + length) ∧
        ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftAnchoredPhysicalSegmentAt
          A strategy hwin policy env
            (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
              strategy hwin policy initialOne initialTwo fallbackLeft
                fallbackRight env)
            anchor (n + length) tableMember twoEnd.2.1.baseShared
              (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverForRecvOne
                A strategy hwin policy oneEnd twoEnd) := by
  induction length generalizing n one two with
  | zero =>
      exact ⟨one, two, hinvariant, by simpa using hpair, by simpa using segment⟩
  | succ length ih =>
      have hgraphNow : (env n).graph = .left := by
        simpa using hgraph 0 (Nat.zero_lt_succ length)
      let fresh :=
        profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair.{u, v, x,
          y, s, max u v x y s, max u v x y s, max u v x y s,
          max u v x y s} A strategy hwin policy fallbackLeft fallbackRight one
            two ((env n).inputOne, (env n).inputTwo)
      let oneNext : OnePending A strategy hwin policy := fresh.1.1.openControl
      let twoNext : TwoPending A strategy hwin policy :=
        (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveTwoPendingStep A
            strategy hwin policy) two (env n).inputTwo).1
      have hinvariantNext := hinvariant.strictLeft A strategy hwin
        fallbackLeft fallbackRight ((env n).inputOne, (env n).inputTwo)
      have hsegmentNext := segment.stepSemantic A strategy hwin policy
        initialOne initialTwo fallbackLeft fallbackRight hinitial env anchor n
          one two hinvariant hpair hgraphNow tableMember
      have hpairNext :
          ((.inl oneNext : OneControl A strategy hwin policy),
              (.inl twoNext : TwoControl A strategy hwin policy)) =
            profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace A
              strategy hwin policy initialOne initialTwo fallbackLeft
                fallbackRight env (n + 1) := by
        simpa
          [profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace,
            FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
            hgraphNow, oneNext, twoNext, fresh]
          using congrArg
            (fun controls : OneControl A strategy hwin policy ×
                TwoControl A strategy hwin policy ↦
              ((profiledRawJointHybridPhysicalCompatiblePhaseLiveOpenRecvOne A
                  strategy hwin policy initialOne fallbackLeft fallbackRight
                    controls.1 (env n).inputOne controls.2
                      (env n).inputTwo).1,
                (profiledRawJointHybridPhysicalCompatiblePhaseLiveNoRecvTwo A
                  strategy hwin policy controls.2 (env n).inputTwo).1))
            hpair
      have htail : ∀ j, j < length →
          (env ((n + 1) + j)).graph = .left := by
        intro j hj
        have h := hgraph (j + 1) (Nat.succ_lt_succ hj)
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      have hrest := ih (n := n + 1) oneNext twoNext hinvariantNext hpairNext
        hsegmentNext htail
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrest

/-! ## Exact scheduled strict blocks -/

/-- Every strict-right successor block carries one selected table anchored at
its operational cut and extended through the complete open part of the block. -/
theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLive_exists_rightAnchoredPhysicalSegmentAt_scheduledClose
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (hinitial :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂)
    (hsegmentInitial :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLivePhysicalSegmentInvariantAt
        A strategy hwin policy env
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
            strategy hwin policy initialOne initialTwo fallbackLeft
              fallbackRight env)
          0 initialOne initialTwo)
    (schedule : OperationalCloseMemberSchedule
      (fun j ↦
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env j).graph))
    (k : Nat)
    (hgraph :
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A strategy
        hwin policy initialOne initialTwo fallbackLeft fallbackRight env
          (schedule.cutPackage.cuts (k + 1))).graph = .right) :
    ∃ (tableMember : Bool)
        (oneEnd : OnePending A strategy hwin policy)
        (twoEnd : TwoPending A strategy hwin policy),
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
          strategy hwin policy oneEnd twoEnd ∧
        ((.inl oneEnd : OneControl A strategy hwin policy),
            (.inl twoEnd : TwoControl A strategy hwin policy)) =
          profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace A
            strategy hwin policy initialOne initialTwo fallbackLeft
              fallbackRight env
                (schedule.cutPackage.cuts (k + 1) +
                  schedule.cutPackage.openLength (k + 1)) ∧
        ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightAnchoredPhysicalSegmentAt
          A strategy hwin policy env
            (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
              strategy hwin policy initialOne initialTwo fallbackLeft
                fallbackRight env)
            (schedule.cutPackage.cuts (k + 1))
            (schedule.cutPackage.cuts (k + 1) +
              schedule.cutPackage.openLength (k + 1))
            tableMember oneEnd.2.1.baseShared
              (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverForRecvTwo
                A strategy hwin policy twoEnd oneEnd) := by
  let start := schedule.cutPackage.cuts (k + 1)
  have hcanonical :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace_physicalSegments
      A strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
        hinitial env hsegmentInitial start
  rcases hcanonical with
    ⟨one, two, hone, htwo, hinvariant, hphysical, _hcanonical⟩
  have hpair :
      ((.inl one : OneControl A strategy hwin policy),
          (.inl two : TwoControl A strategy hwin policy)) =
        profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env start := by
    apply Prod.ext
    · exact hone.symm
    · exact htwo.symm
  have hselected := hphysical.right_selected A strategy hwin
  have hanchored := hselected.anchoredAt_successorCut A strategy hwin schedule k
    rfl hgraph
  have hhomogeneous : ∀ j, j < schedule.cutPackage.openLength (k + 1) →
      (env (start + j)).graph = .right := by
    intro j hj
    have h := schedule.cutPackage.homogeneous (k + 1) j hj
    have hword := h.trans hgraph
    simpa [start,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord] using
        hword
  refine ⟨one.1, ?_⟩
  simpa [start] using
    hanchored.homogeneous A strategy hwin policy initialOne initialTwo
      fallbackLeft fallbackRight hinitial env start start
        (schedule.cutPackage.openLength (k + 1)) one two hinvariant hpair one.1
          hhomogeneous

/-- Left-oriented scheduled-block mirror. -/
theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLive_exists_leftAnchoredPhysicalSegmentAt_scheduledClose
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (hinitial :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂)
    (hsegmentInitial :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLivePhysicalSegmentInvariantAt
        A strategy hwin policy env
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
            strategy hwin policy initialOne initialTwo fallbackLeft
              fallbackRight env)
          0 initialOne initialTwo)
    (schedule : OperationalCloseMemberSchedule
      (fun j ↦
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env j).graph))
    (k : Nat)
    (hgraph :
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A strategy
        hwin policy initialOne initialTwo fallbackLeft fallbackRight env
          (schedule.cutPackage.cuts (k + 1))).graph = .left) :
    ∃ (tableMember : Bool)
        (oneEnd : OnePending A strategy hwin policy)
        (twoEnd : TwoPending A strategy hwin policy),
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
          strategy hwin policy oneEnd twoEnd ∧
        ((.inl oneEnd : OneControl A strategy hwin policy),
            (.inl twoEnd : TwoControl A strategy hwin policy)) =
          profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace A
            strategy hwin policy initialOne initialTwo fallbackLeft
              fallbackRight env
                (schedule.cutPackage.cuts (k + 1) +
                  schedule.cutPackage.openLength (k + 1)) ∧
        ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftAnchoredPhysicalSegmentAt
          A strategy hwin policy env
            (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
              strategy hwin policy initialOne initialTwo fallbackLeft
                fallbackRight env)
            (schedule.cutPackage.cuts (k + 1))
            (schedule.cutPackage.cuts (k + 1) +
              schedule.cutPackage.openLength (k + 1))
            tableMember twoEnd.2.1.baseShared
              (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverForRecvOne
                A strategy hwin policy oneEnd twoEnd) := by
  let start := schedule.cutPackage.cuts (k + 1)
  have hcanonical :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace_physicalSegments
      A strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
        hinitial env hsegmentInitial start
  rcases hcanonical with
    ⟨one, two, hone, htwo, hinvariant, hphysical, _hcanonical⟩
  have hpair :
      ((.inl one : OneControl A strategy hwin policy),
          (.inl two : TwoControl A strategy hwin policy)) =
        profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env start := by
    apply Prod.ext
    · exact hone.symm
    · exact htwo.symm
  have hselected := hphysical.left_selected A strategy hwin
  have hanchored := hselected.anchoredAt_successorCut A strategy hwin schedule k
    rfl hgraph
  have hhomogeneous : ∀ j, j < schedule.cutPackage.openLength (k + 1) →
      (env (start + j)).graph = .left := by
    intro j hj
    have h := schedule.cutPackage.homogeneous (k + 1) j hj
    have hword := h.trans hgraph
    simpa [start,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord] using
        hword
  refine ⟨two.1, ?_⟩
  simpa [start] using
    hanchored.homogeneous A strategy hwin policy initialOne initialTwo
      fallbackLeft fallbackRight hinitial env start start
        (schedule.cutPackage.openLength (k + 1)) one two hinvariant hpair two.1
          hhomogeneous

/-! ## Literal strict successor-cut packages -/

/-- A strict-right scheduled successor block supplies both the complete open
literal prefix and its exact physical closing record. -/
theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLive_exists_rightLiteralStrictSuccessorBlockAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (hinitial :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂)
    (hsegmentInitial :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLivePhysicalSegmentInvariantAt
        A strategy hwin policy env
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
            strategy hwin policy initialOne initialTwo fallbackLeft
              fallbackRight env)
          0 initialOne initialTwo)
    (schedule : OperationalCloseMemberSchedule
      (fun j ↦
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env j).graph))
    (k : Nat)
    (hgraph :
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A strategy
        hwin policy initialOne initialTwo fallbackLeft fallbackRight env
          (schedule.cutPackage.cuts (k + 1))).graph = .right) :
    ∃ (state : CompatibleState A strategy hwin initial)
        (move : ProfiledRawJointRightPhysicalSiblingMove A)
        (tableMember : Bool) (row : PairedEntryRow)
        (ownerControl : (move.memberController A false).Control)
        (monitorState :
          (profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A
            strategy hwin (initial := initial) move false).State),
      ProfiledRawJointHybridPhysicalCompatibleRightLiteralPrefixAt A strategy
          hwin policy state move tableMember row
            (fun j ↦
              ((env (schedule.cutPackage.cuts (k + 1) + j)).inputTwo,
                (env (schedule.cutPackage.cuts (k + 1) + j)).inputOne))
            ownerControl monitorState
            (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
              strategy hwin policy initialOne initialTwo fallbackLeft
                fallbackRight env)
            (schedule.cutPackage.cuts (k + 1))
            (schedule.cutPackage.openLength (k + 1)) ∧
        profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
            strategy hwin policy initialOne initialTwo fallbackLeft
              fallbackRight env (schedule.cutPackage.cuts (k + 2) - 1) =
          profiledRawJointTargetRightClosingRecordForMember
            (schedule.closeMember (k + 1)) row
            (profiledRawJointTargetRightPhysicalLetter A
              (profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A
                strategy hwin policy state move tableMember
                  (fun j ↦
                    ((env (schedule.cutPackage.cuts (k + 1) + j)).inputTwo,
                      (env (schedule.cutPackage.cuts (k + 1) + j)).inputOne))
                  (schedule.cutPackage.openLength (k + 1)))) := by
  let word :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A strategy
      hwin policy initialOne initialTwo fallbackLeft fallbackRight env
  let start := schedule.cutPackage.cuts (k + 1)
  let length := schedule.cutPackage.openLength (k + 1)
  obtain ⟨tableMember, oneEnd, twoEnd, hinvariantEnd, hpairEnd,
      hanchoredEnd⟩ :=
    profiledRawJointHybridPhysicalCompatiblePhaseLive_exists_rightAnchoredPhysicalSegmentAt_scheduledClose
      A strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
        hinitial env hsegmentInitial schedule k hgraph
  have hclosingIndex : start + length =
      schedule.cutPackage.cuts (k + 2) - 1 := by
    exact schedule.start_add_openLength_eq_closingIndex (k + 1)
  have hgraphEnd : (env (start + length)).graph = .right := by
    have hclose := schedule.cutPackage.closing_graph_eq (k + 1)
    have hword : (word (schedule.cutPackage.cuts (k + 2) - 1)).graph =
        .right := hclose.trans hgraph
    rw [← hclosingIndex] at hword
    simpa [word,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord] using
        hword
  obtain ⟨state, move, ownerControl, row, monitorState, staged, _howner,
      _hreceiver, hliteral, hrecord⟩ :=
    hanchoredEnd.currentRecord_eq A strategy hwin policy initialOne initialTwo
      fallbackLeft fallbackRight hinitial env start (start + length) oneEnd
        twoEnd hinvariantEnd hpairEnd hgraphEnd tableMember
  have hgraphStart : (word start).graph = .right := by
    simpa [start, word] using hgraph
  have hmember : schedule.closeMember (k + 1) = false :=
    (schedule.closeMember_eq_false_iff (k + 1)).mpr (by
      intro hboth
      exact Graph.noConfusion (hgraphStart.symm.trans hboth))
  refine ⟨state, move, tableMember, row, ownerControl, monitorState, ?_, ?_⟩
  · simpa [start, length] using hliteral
  · rw [hmember]
    rw [← hclosingIndex]
    simpa [start, length] using hrecord

/-- Strict-left literal successor block. -/
theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLive_exists_leftLiteralStrictSuccessorBlockAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (hinitial :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂)
    (hsegmentInitial :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLivePhysicalSegmentInvariantAt
        A strategy hwin policy env
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
            strategy hwin policy initialOne initialTwo fallbackLeft
              fallbackRight env)
          0 initialOne initialTwo)
    (schedule : OperationalCloseMemberSchedule
      (fun j ↦
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env j).graph))
    (k : Nat)
    (hgraph :
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A strategy
        hwin policy initialOne initialTwo fallbackLeft fallbackRight env
          (schedule.cutPackage.cuts (k + 1))).graph = .left) :
    ∃ (state : CompatibleState A strategy hwin initial)
        (move : ProfiledRawJointLeftPhysicalSiblingMove A)
        (tableMember : Bool) (row : PairedEntryRow)
        (ownerControl : (move.memberController A false).Control)
        (monitorState :
          (profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A
            strategy hwin (initial := initial) move false).State),
      ProfiledRawJointHybridPhysicalCompatibleLeftLiteralPrefixAt A strategy
          hwin policy state move tableMember row
            (fun j ↦
              ((env (schedule.cutPackage.cuts (k + 1) + j)).inputOne,
                (env (schedule.cutPackage.cuts (k + 1) + j)).inputTwo))
            ownerControl monitorState
            (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
              strategy hwin policy initialOne initialTwo fallbackLeft
                fallbackRight env)
            (schedule.cutPackage.cuts (k + 1))
            (schedule.cutPackage.openLength (k + 1)) ∧
        profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
            strategy hwin policy initialOne initialTwo fallbackLeft
              fallbackRight env (schedule.cutPackage.cuts (k + 2) - 1) =
          profiledRawJointTargetLeftClosingRecordForMember
            (schedule.closeMember (k + 1)) row
            (profiledRawJointTargetLeftPhysicalLetter A
              (profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A
                strategy hwin policy state move tableMember
                  (fun j ↦
                    ((env (schedule.cutPackage.cuts (k + 1) + j)).inputOne,
                      (env (schedule.cutPackage.cuts (k + 1) + j)).inputTwo))
                  (schedule.cutPackage.openLength (k + 1)))) := by
  let word :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A strategy
      hwin policy initialOne initialTwo fallbackLeft fallbackRight env
  let start := schedule.cutPackage.cuts (k + 1)
  let length := schedule.cutPackage.openLength (k + 1)
  obtain ⟨tableMember, oneEnd, twoEnd, hinvariantEnd, hpairEnd,
      hanchoredEnd⟩ :=
    profiledRawJointHybridPhysicalCompatiblePhaseLive_exists_leftAnchoredPhysicalSegmentAt_scheduledClose
      A strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
        hinitial env hsegmentInitial schedule k hgraph
  have hclosingIndex : start + length =
      schedule.cutPackage.cuts (k + 2) - 1 := by
    exact schedule.start_add_openLength_eq_closingIndex (k + 1)
  have hgraphEnd : (env (start + length)).graph = .left := by
    have hclose := schedule.cutPackage.closing_graph_eq (k + 1)
    have hword : (word (schedule.cutPackage.cuts (k + 2) - 1)).graph =
        .left := hclose.trans hgraph
    rw [← hclosingIndex] at hword
    simpa [word,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord] using
        hword
  obtain ⟨state, move, ownerControl, row, monitorState, staged, _howner,
      _hreceiver, hliteral, hrecord⟩ :=
    hanchoredEnd.currentRecord_eq A strategy hwin policy initialOne initialTwo
      fallbackLeft fallbackRight hinitial env start (start + length) oneEnd
        twoEnd hinvariantEnd hpairEnd hgraphEnd tableMember
  have hgraphStart : (word start).graph = .left := by
    simpa [start, word] using hgraph
  have hmember : schedule.closeMember (k + 1) = false :=
    (schedule.closeMember_eq_false_iff (k + 1)).mpr (by
      intro hboth
      exact Graph.noConfusion (hgraphStart.symm.trans hboth))
  refine ⟨state, move, tableMember, row, ownerControl, monitorState, ?_, ?_⟩
  · simpa [start, length] using hliteral
  · rw [hmember]
    rw [← hclosingIndex]
    simpa [start, length] using hrecord

/-! ## Scheduled-alignment corollaries -/

/-- In a strict-right successor block, the phase-live trace discharges every
scheduled-alignment field except the DPA entry-state equality supplied by the
lineage induction. -/
theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLive_exists_rightScheduledAlignmentAt_of_strict
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (hinitial :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂)
    (hsegmentInitial :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLivePhysicalSegmentInvariantAt
        A strategy hwin policy env
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
            strategy hwin policy initialOne initialTwo fallbackLeft
              fallbackRight env)
          0 initialOne initialTwo)
    (schedule : OperationalCloseMemberSchedule
      (fun j ↦
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env j).graph))
    (physicalState : A.State) (k : Nat)
    (hgraph :
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A strategy
        hwin policy initialOne initialTwo fallbackLeft fallbackRight env
          (schedule.cutPackage.cuts (k + 1))).graph = .right) :
    ∃ (state : CompatibleState A strategy hwin initial)
        (move : ProfiledRawJointRightPhysicalSiblingMove A)
        (tableMember : Bool) (row : PairedEntryRow),
      let localEnv : Nat → In₂ × In₁ := fun j ↦
        ((env (schedule.cutPackage.cuts (k + 1) + j)).inputTwo,
          (env (schedule.cutPackage.cuts (k + 1) + j)).inputOne)
      A.runFrom physicalState
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
            strategy hwin policy initialOne initialTwo fallbackLeft
              fallbackRight env)
          (schedule.cutPackage.cuts (k + 1)) =
          pairedCodeStateForRow A row move.1.source.1.1 →
        ProfiledRawJointHybridPhysicalCompatibleRightScheduledAlignmentAt A
          strategy hwin policy state move tableMember row localEnv
            (schedule.cutPackage.openLength (k + 1)) physicalState
            (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
              strategy hwin policy initialOne initialTwo fallbackLeft
                fallbackRight env)
            schedule (k + 1) := by
  obtain ⟨state, move, tableMember, row, ownerControl, monitorState,
      hliteral, hclosing⟩ :=
    profiledRawJointHybridPhysicalCompatiblePhaseLive_exists_rightLiteralStrictSuccessorBlockAt
      A strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
        hinitial env hsegmentInitial schedule k hgraph
  refine ⟨state, move, tableMember, row, ?_⟩
  dsimp only
  intro hentry
  apply hliteral.toScheduledAlignment A strategy hwin rfl
  · intro _hne
    exact hgraph
  · exact hentry
  · have hinputs := congrArg
      (fun record : RoundRecord In₁ In₂ Graph Out₁ Out₂ ↦
        (record.inputTwo, record.inputOne)) hclosing
    simpa using hinputs
  · exact congrArg RoundRecord.outputPair hclosing

/-- Left scheduled-alignment mirror. -/
theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLive_exists_leftScheduledAlignmentAt_of_strict
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (hinitial :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂)
    (hsegmentInitial :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLivePhysicalSegmentInvariantAt
        A strategy hwin policy env
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
            strategy hwin policy initialOne initialTwo fallbackLeft
              fallbackRight env)
          0 initialOne initialTwo)
    (schedule : OperationalCloseMemberSchedule
      (fun j ↦
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env j).graph))
    (physicalState : A.State) (k : Nat)
    (hgraph :
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A strategy
        hwin policy initialOne initialTwo fallbackLeft fallbackRight env
          (schedule.cutPackage.cuts (k + 1))).graph = .left) :
    ∃ (state : CompatibleState A strategy hwin initial)
        (move : ProfiledRawJointLeftPhysicalSiblingMove A)
        (tableMember : Bool) (row : PairedEntryRow),
      let localEnv : Nat → In₁ × In₂ := fun j ↦
        ((env (schedule.cutPackage.cuts (k + 1) + j)).inputOne,
          (env (schedule.cutPackage.cuts (k + 1) + j)).inputTwo)
      A.runFrom physicalState
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
            strategy hwin policy initialOne initialTwo fallbackLeft
              fallbackRight env)
          (schedule.cutPackage.cuts (k + 1)) =
          pairedCodeStateForRow A row move.1.source.1.1 →
        ProfiledRawJointHybridPhysicalCompatibleLeftScheduledAlignmentAt A
          strategy hwin policy state move tableMember row localEnv
            (schedule.cutPackage.openLength (k + 1)) physicalState
            (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
              strategy hwin policy initialOne initialTwo fallbackLeft
                fallbackRight env)
            schedule (k + 1) := by
  obtain ⟨state, move, tableMember, row, ownerControl, monitorState,
      hliteral, hclosing⟩ :=
    profiledRawJointHybridPhysicalCompatiblePhaseLive_exists_leftLiteralStrictSuccessorBlockAt
      A strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
        hinitial env hsegmentInitial schedule k hgraph
  refine ⟨state, move, tableMember, row, ?_⟩
  dsimp only
  intro hentry
  apply hliteral.toScheduledAlignment A strategy hwin rfl
  · intro _hne
    exact hgraph
  · exact hentry
  · have hinputs := congrArg
      (fun record : RoundRecord In₁ In₂ Graph Out₁ Out₂ ↦
        (record.inputOne, record.inputTwo)) hclosing
    simpa using hinputs
  · exact congrArg RoundRecord.outputPair hclosing

/-! ## Same-policy successor installed by a strict close -/

/-- The exact target selected by the live right table is definitionally the
compatible-policy state installed in process two's open continuation. -/
theorem
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant.strictRight_targetAt_and_nextState
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {one : OnePending A strategy hwin policy}
    {two : TwoPending A strategy hwin policy}
    (hinvariant :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy one two)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (input : In₁ × In₂) :
    let receiver :=
      profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverForRecvTwo
        A strategy hwin policy two one
    let row :=
      profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverRow A
        strategy hwin receiver
    let output :=
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvTwoRight A strategy
        hwin policy fallbackRight two one (input.2, input.1)).1
    let payload :=
      profiledRawJointHybridPhysicalCompatibleRightPendingPayloadOfOutput A
        strategy hwin output row
    let target :=
      profiledRawJointHybridPhysicalCompatibleRightPendingPayloadTarget A
        strategy hwin payload false
    let fresh :=
      profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair.{u, v, x, y,
        s, max u v x y s, max u v x y s, max u v x y s,
        max u v x y s} A strategy hwin policy fallbackLeft fallbackRight one two
          input
    ∃ slot : ProfiledRawLeftSlot A,
      ProfiledRawJointHybridPhysicalCompatibleRootAlignedSuccessorTargetAt A
          strategy hwin policy one.2.1.baseShared.1 target .left (.inr slot) ∧
        fresh.1.2.openControl.2.1.baseShared.1 =
          profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
            hwin target := by
  dsimp only
  let selected := hinvariant.right_selected A strategy hwin
  obtain ⟨slot, htarget⟩ :=
    selected.exists_rootAlignedTargetAt A strategy hwin fallbackRight
      (input.2, input.1) false
  refine ⟨slot, htarget, ?_⟩
  rfl

/-- Strict-left mirror. -/
theorem
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant.strictLeft_targetAt_and_nextState
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {one : OnePending A strategy hwin policy}
    {two : TwoPending A strategy hwin policy}
    (hinvariant :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy one two)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (input : In₁ × In₂) :
    let receiver :=
      profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverForRecvOne A
        strategy hwin policy one two
    let row :=
      profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverRow A
        strategy hwin receiver
    let output :=
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvOneLeft A strategy
        hwin policy fallbackLeft one two input).1
    let payload :=
      profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadOfOutput A
        strategy hwin output row
    let target :=
      profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadTarget A
        strategy hwin payload false
    let fresh :=
      profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair.{u, v, x, y,
        s, max u v x y s, max u v x y s, max u v x y s,
        max u v x y s} A strategy hwin policy fallbackLeft fallbackRight one two
          input
    ∃ slot : ProfiledRawRightSlot A,
      ProfiledRawJointHybridPhysicalCompatibleRootAlignedSuccessorTargetAt A
          strategy hwin policy two.2.1.baseShared.1 target .right (.inl slot) ∧
        fresh.1.1.openControl.2.1.baseShared.1 =
          profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
            hwin target := by
  dsimp only
  let selected := hinvariant.left_selected A strategy hwin
  obtain ⟨slot, htarget⟩ :=
    selected.exists_rootAlignedTargetAt A strategy hwin fallbackLeft input
      false
  refine ⟨slot, htarget, ?_⟩
  rfl

/-- The target certificate exposed by a selected anchored right epoch is the
target of the very decorated table letter used by its physical cut packet. -/
theorem
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightAnchoredPhysicalSegmentAt.exists_currentTargetAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (hinitial :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂) (start n : Nat)
    (one : OnePending A strategy hwin policy)
    (two : TwoPending A strategy hwin policy)
    (hinvariant :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy one two)
    (hpair :
      ((.inl one : OneControl A strategy hwin policy),
          (.inl two : TwoControl A strategy hwin policy)) =
        profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env n)
    (hgraph : (env n).graph = .right)
    (tableMember : Bool)
    (segment :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightAnchoredPhysicalSegmentAt
        A strategy hwin policy env
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
            strategy hwin policy initialOne initialTwo fallbackLeft
              fallbackRight env)
          start n tableMember one.2.1.baseShared
            (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverForRecvTwo
              A strategy hwin policy two one)) :
    ∃ (state : CompatibleState A strategy hwin initial)
        (move : ProfiledRawJointRightPhysicalSiblingMove A)
        (ownerControl : (move.memberController A false).Control)
        (row : PairedEntryRow)
        (monitorState :
          (profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A
            strategy hwin (initial := initial) move false).State)
        (staged : Option (RightOutput A strategy hwin initial)),
      ProfiledRawJointHybridPhysicalCompatibleRightLiteralPrefixAt A strategy
            hwin policy state move tableMember row
              (fun j ↦ ((env (start + j)).inputTwo,
                (env (start + j)).inputOne))
              ownerControl monitorState
              (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
                strategy hwin policy initialOne initialTwo fallbackLeft
                  fallbackRight env)
              start (n - start) ∧
        profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
              strategy hwin policy initialOne initialTwo fallbackLeft
                fallbackRight env n =
            profiledRawJointTargetRightClosingRecordForMember false row
              (profiledRawJointTargetRightPhysicalLetter A
                (profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A
                  strategy hwin policy state move tableMember
                    (fun j ↦ ((env (start + j)).inputTwo,
                      (env (start + j)).inputOne)) (n - start))) ∧
        ∃ slot : ProfiledRawLeftSlot A,
          ProfiledRawJointHybridPhysicalCompatibleRootAlignedSuccessorTargetAt
            A strategy hwin policy state
              (((profiledRawJointHybridPhysicalCompatibleRightDecoratedPlay A
                strategy hwin policy state move tableMember
                  (fun j ↦ ((env (start + j)).inputTwo,
                    (env (start + j)).inputOne)) (n - start)).2.1.target row).1)
              .left (.inr slot) ∧
            let fresh :=
              profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair.{u,
                v, x, y, s, max u v x y s, max u v x y s,
                max u v x y s, max u v x y s} A strategy hwin policy
                fallbackLeft fallbackRight one two
                  ((env n).inputOne, (env n).inputTwo)
            fresh.1.2.openControl.2.1.baseShared.1 =
              profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A
                strategy hwin
                  (((profiledRawJointHybridPhysicalCompatibleRightDecoratedPlay
                    A strategy hwin policy state move tableMember
                      (fun j ↦ ((env (start + j)).inputTwo,
                        (env (start + j)).inputOne))
                      (n - start)).2.1.target row).1) := by
  obtain ⟨state, move, ownerControl, row, monitorState, staged, howner,
      hreceiver, hliteral, hrecord⟩ :=
    segment.currentRecord_eq A strategy hwin policy initialOne initialTwo
      fallbackLeft fallbackRight hinitial env start n one two hinvariant hpair
        hgraph tableMember
  let localEnv : Nat → In₂ × In₁ :=
    fun j ↦ ((env (start + j)).inputTwo, (env (start + j)).inputOne)
  have houtput :=
    hliteral.literal_reachable.output_eq_play_of_prefix A strategy hwin
      tableMember row localEnv (n - start) rfl
  obtain ⟨slot, htarget, hnext⟩ :=
    hinvariant.strictRight_targetAt_and_nextState A strategy hwin fallbackLeft
      fallbackRight ((env n).inputOne, (env n).inputTwo)
  have hphaseRow :
      profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverRow A
          strategy hwin
            (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverForRecvTwo
              A strategy hwin policy two one) = row := by
    rw [hreceiver]
    simp
  have hselectedOutput :
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvTwoRight A strategy
          hwin policy fallbackRight two one
            ((env n).inputTwo, (env n).inputOne)).1 =
        (profiledRawJointHybridPhysicalCompatibleRightReceiverStepFor A strategy
          hwin policy state move ownerControl row monitorState
            ((env n).inputTwo, (env n).inputOne)).1 := by
    simp only
      [profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvTwoRight]
    rw [howner, hreceiver]
    simp
  rw [howner, hphaseRow, hselectedOutput] at htarget
  rw [hphaseRow, hselectedOutput] at hnext
  simp only
    [profiledRawJointHybridPhysicalCompatibleRightPendingPayloadOfOutput_target]
    at htarget hnext
  have hindex : start + (n - start) = n := by
    exact Nat.add_sub_of_le segment.1
  have hlocalInput : localEnv (n - start) =
      ((env n).inputTwo, (env n).inputOne) := by
    simp only [localEnv, hindex]
  rw [hlocalInput] at houtput
  rw [houtput] at htarget
  rw [houtput] at hnext
  exact ⟨state, move, ownerControl, row, monitorState, staged,
    by simpa [localEnv] using hliteral,
    by simpa [localEnv,
      profiledRawJointTargetRightClosingRecordForMember] using hrecord,
    slot, by simpa [localEnv] using htarget,
    by simpa [localEnv] using hnext⟩

/-- Left anchored epoch exposes the exact decorated successor target. -/
theorem
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftAnchoredPhysicalSegmentAt.exists_currentTargetAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (hinitial :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂) (start n : Nat)
    (one : OnePending A strategy hwin policy)
    (two : TwoPending A strategy hwin policy)
    (hinvariant :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy one two)
    (hpair :
      ((.inl one : OneControl A strategy hwin policy),
          (.inl two : TwoControl A strategy hwin policy)) =
        profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env n)
    (hgraph : (env n).graph = .left)
    (tableMember : Bool)
    (segment :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftAnchoredPhysicalSegmentAt
        A strategy hwin policy env
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
            strategy hwin policy initialOne initialTwo fallbackLeft
              fallbackRight env)
          start n tableMember two.2.1.baseShared
            (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverForRecvOne
              A strategy hwin policy one two)) :
    ∃ (state : CompatibleState A strategy hwin initial)
        (move : ProfiledRawJointLeftPhysicalSiblingMove A)
        (ownerControl : (move.memberController A false).Control)
        (row : PairedEntryRow)
        (monitorState :
          (profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A
            strategy hwin (initial := initial) move false).State)
        (staged : Option (LeftOutput A strategy hwin initial)),
      ProfiledRawJointHybridPhysicalCompatibleLeftLiteralPrefixAt A strategy
            hwin policy state move tableMember row
              (fun j ↦ ((env (start + j)).inputOne,
                (env (start + j)).inputTwo))
              ownerControl monitorState
              (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
                strategy hwin policy initialOne initialTwo fallbackLeft
                  fallbackRight env)
              start (n - start) ∧
        profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
              strategy hwin policy initialOne initialTwo fallbackLeft
                fallbackRight env n =
            profiledRawJointTargetLeftClosingRecordForMember false row
              (profiledRawJointTargetLeftPhysicalLetter A
                (profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A
                  strategy hwin policy state move tableMember
                    (fun j ↦ ((env (start + j)).inputOne,
                      (env (start + j)).inputTwo)) (n - start))) ∧
        ∃ slot : ProfiledRawRightSlot A,
          ProfiledRawJointHybridPhysicalCompatibleRootAlignedSuccessorTargetAt
            A strategy hwin policy state
              (((profiledRawJointHybridPhysicalCompatibleLeftDecoratedPlay A
                strategy hwin policy state move tableMember
                  (fun j ↦ ((env (start + j)).inputOne,
                    (env (start + j)).inputTwo)) (n - start)).2.1.target row).1)
              .right (.inl slot) ∧
            let fresh :=
              profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair.{u,
                v, x, y, s, max u v x y s, max u v x y s,
                max u v x y s, max u v x y s} A strategy hwin policy
                fallbackLeft fallbackRight one two
                  ((env n).inputOne, (env n).inputTwo)
            fresh.1.1.openControl.2.1.baseShared.1 =
              profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A
                strategy hwin
                  (((profiledRawJointHybridPhysicalCompatibleLeftDecoratedPlay
                    A strategy hwin policy state move tableMember
                      (fun j ↦ ((env (start + j)).inputOne,
                        (env (start + j)).inputTwo))
                      (n - start)).2.1.target row).1) := by
  obtain ⟨state, move, ownerControl, row, monitorState, staged, howner,
      hreceiver, hliteral, hrecord⟩ :=
    segment.currentRecord_eq A strategy hwin policy initialOne initialTwo
      fallbackLeft fallbackRight hinitial env start n one two hinvariant hpair
        hgraph tableMember
  let localEnv : Nat → In₁ × In₂ :=
    fun j ↦ ((env (start + j)).inputOne, (env (start + j)).inputTwo)
  have houtput :=
    hliteral.literal_reachable.output_eq_play_of_prefix A strategy hwin
      tableMember row localEnv (n - start) rfl
  obtain ⟨slot, htarget, hnext⟩ :=
    hinvariant.strictLeft_targetAt_and_nextState A strategy hwin fallbackLeft
      fallbackRight ((env n).inputOne, (env n).inputTwo)
  have hphaseRow :
      profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverRow A
          strategy hwin
            (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverForRecvOne
              A strategy hwin policy one two) = row := by
    rw [hreceiver]
    simp
  have hselectedOutput :
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvOneLeft A strategy
          hwin policy fallbackLeft one two
            ((env n).inputOne, (env n).inputTwo)).1 =
        (profiledRawJointHybridPhysicalCompatibleLeftReceiverStepFor A strategy
          hwin policy state move ownerControl row monitorState
            ((env n).inputOne, (env n).inputTwo)).1 := by
    simp only
      [profiledRawJointHybridPhysicalCompatiblePhaseLiveRecvOneLeft]
    rw [howner, hreceiver]
    simp
  rw [howner, hphaseRow, hselectedOutput] at htarget
  rw [hphaseRow, hselectedOutput] at hnext
  simp only
    [profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadOfOutput_target]
    at htarget hnext
  have hindex : start + (n - start) = n := by
    exact Nat.add_sub_of_le segment.1
  have hlocalInput : localEnv (n - start) =
      ((env n).inputOne, (env n).inputTwo) := by
    simp only [localEnv, hindex]
  rw [hlocalInput] at houtput
  rw [houtput] at htarget
  rw [houtput] at hnext
  exact ⟨state, move, ownerControl, row, monitorState, staged,
    by simpa [localEnv] using hliteral,
    by simpa [localEnv,
      profiledRawJointTargetLeftClosingRecordForMember] using hrecord,
    slot, by simpa [localEnv] using htarget,
    by simpa [localEnv] using hnext⟩

/-! ## Strict successor lineage at schedule indices -/

/-- A complete strict-right successor block, indexed exactly as the resolved
transition stream.  Besides the physical packet, this retains the selected
semantic controls immediately before and after the closing round. -/
structure
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightStrictSuccessorLineageAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (env : EnvironmentSequence In₁ In₂)
    (schedule : OperationalCloseMemberSchedule
      (fun j ↦
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env j).graph))
    (k : Nat)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (tableMember : Bool) (row : PairedEntryRow)
    (ownerControl : (move.memberController A false).Control)
    (monitorState :
    (profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A strategy
      hwin (initial := initial) move false).State)
    (oneEnd : OnePending A strategy hwin policy)
    (twoEnd : TwoPending A strategy hwin policy)
    (oneNext : OnePending A strategy hwin policy)
    (twoNext : TwoPending A strategy hwin policy) : Prop where
  invariantEnd :
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A strategy
      hwin policy oneEnd twoEnd
  selectedEnd :
    ((.inl oneEnd : OneControl A strategy hwin policy),
        (.inl twoEnd : TwoControl A strategy hwin policy)) =
      profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace A strategy
        hwin policy initialOne initialTwo fallbackLeft fallbackRight env
          (schedule.cutPackage.cuts (k + 2) - 1)
  literalPrefix :
    ProfiledRawJointHybridPhysicalCompatibleRightLiteralPrefixAt A strategy
      hwin policy state move tableMember row
        (fun j ↦
          ((env (schedule.cutPackage.cuts (k + 1) + j)).inputTwo,
            (env (schedule.cutPackage.cuts (k + 1) + j)).inputOne))
        ownerControl monitorState
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env)
        (schedule.cutPackage.cuts (k + 1))
        (schedule.cutPackage.openLength (k + 1))
  closingRecord :
    profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A strategy
        hwin policy initialOne initialTwo fallbackLeft fallbackRight env
          (schedule.cutPackage.cuts (k + 2) - 1) =
      profiledRawJointTargetRightClosingRecordForMember false row
        (profiledRawJointTargetRightPhysicalLetter A
          (profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A strategy
            hwin policy state move tableMember
              (fun j ↦
                ((env (schedule.cutPackage.cuts (k + 1) + j)).inputTwo,
                  (env (schedule.cutPackage.cuts (k + 1) + j)).inputOne))
              (schedule.cutPackage.openLength (k + 1))))
  invariantNext :
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A strategy
      hwin policy oneNext twoNext
  selectedNext :
    ((.inl oneNext : OneControl A strategy hwin policy),
        (.inl twoNext : TwoControl A strategy hwin policy)) =
      profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace A strategy
        hwin policy initialOne initialTwo fallbackLeft fallbackRight env
          (schedule.cutPackage.cuts (k + 2))
  successor :
    ∃ slot : ProfiledRawLeftSlot A,
      ProfiledRawJointHybridPhysicalCompatibleRootAlignedSuccessorTargetAt A
          strategy hwin policy state
            (((profiledRawJointHybridPhysicalCompatibleRightDecoratedPlay A
              strategy hwin policy state move tableMember
                (fun j ↦
                  ((env (schedule.cutPackage.cuts (k + 1) + j)).inputTwo,
                    (env (schedule.cutPackage.cuts (k + 1) + j)).inputOne))
                (schedule.cutPackage.openLength (k + 1))).2.1.target row).1)
            .left (.inr slot) ∧
        twoNext.2.1.baseShared.1 =
          profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
            hwin
              (((profiledRawJointHybridPhysicalCompatibleRightDecoratedPlay A
                strategy hwin policy state move tableMember
                  (fun j ↦
                    ((env (schedule.cutPackage.cuts (k + 1) + j)).inputTwo,
                      (env (schedule.cutPackage.cuts (k + 1) + j)).inputOne))
                  (schedule.cutPackage.openLength (k + 1))).2.1.target row).1)

/-- Every scheduled strict-right successor block has the complete lineage
package above. -/
theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLive_exists_rightStrictSuccessorLineageAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (hinitial :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂)
    (hsegmentInitial :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLivePhysicalSegmentInvariantAt
        A strategy hwin policy env
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
            strategy hwin policy initialOne initialTwo fallbackLeft
              fallbackRight env)
          0 initialOne initialTwo)
    (schedule : OperationalCloseMemberSchedule
      (fun j ↦
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env j).graph))
    (k : Nat)
    (hgraph :
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A strategy
        hwin policy initialOne initialTwo fallbackLeft fallbackRight env
          (schedule.cutPackage.cuts (k + 1))).graph = .right) :
    ∃ (state : CompatibleState A strategy hwin initial)
        (move : ProfiledRawJointRightPhysicalSiblingMove A)
        (tableMember : Bool) (row : PairedEntryRow)
        (ownerControl : (move.memberController A false).Control)
        (monitorState :
          (profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A
            strategy hwin (initial := initial) move false).State)
        (oneEnd : OnePending A strategy hwin policy)
        (twoEnd : TwoPending A strategy hwin policy)
        (oneNext : OnePending A strategy hwin policy)
        (twoNext : TwoPending A strategy hwin policy),
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightStrictSuccessorLineageAt
        A strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
          env schedule k state move tableMember row ownerControl monitorState
            oneEnd twoEnd oneNext twoNext := by
  let word :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A strategy
      hwin policy initialOne initialTwo fallbackLeft fallbackRight env
  let start := schedule.cutPackage.cuts (k + 1)
  let length := schedule.cutPackage.openLength (k + 1)
  let close := schedule.cutPackage.cuts (k + 2) - 1
  obtain ⟨tableMember, oneEnd, twoEnd, hinvariantEnd, hpairEnd,
      hanchoredEnd⟩ :=
    profiledRawJointHybridPhysicalCompatiblePhaseLive_exists_rightAnchoredPhysicalSegmentAt_scheduledClose
      A strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
        hinitial env hsegmentInitial schedule k hgraph
  have hclosingIndex : start + length = close := by
    exact schedule.start_add_openLength_eq_closingIndex (k + 1)
  have hpairClose := hpairEnd
  rw [hclosingIndex] at hpairClose
  have hwordGraphClose : (word close).graph = .right := by
    have hclose := schedule.cutPackage.closing_graph_eq (k + 1)
    exact hclose.trans hgraph
  have henvGraphClose : (env close).graph = .right := by
    simpa [word,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord] using
        hwordGraphClose
  have hanchoredClose :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightAnchoredPhysicalSegmentAt
        A strategy hwin policy env word start close tableMember
          oneEnd.2.1.baseShared
            (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverForRecvTwo
              A strategy hwin policy twoEnd oneEnd) := by
    simpa [word, start, length, close, hclosingIndex] using hanchoredEnd
  obtain ⟨state, move, ownerControl, row, monitorState, staged, hliteral,
      hclosing, slot, htarget, hnext⟩ :=
    hanchoredClose.exists_currentTargetAt A strategy hwin policy initialOne
      initialTwo fallbackLeft fallbackRight hinitial env start close oneEnd
        twoEnd hinvariantEnd hpairClose henvGraphClose tableMember
  let fresh :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair.{u, v, x, y, s,
      max u v x y s, max u v x y s, max u v x y s,
      max u v x y s} A strategy hwin policy fallbackLeft fallbackRight oneEnd
        twoEnd ((env close).inputOne, (env close).inputTwo)
  let oneNext : OnePending A strategy hwin policy :=
    (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveOnePendingStep A
        strategy hwin policy) oneEnd (env close).inputOne).1
  let twoNext : TwoPending A strategy hwin policy := fresh.1.2.openControl
  have hinvariantNext := hinvariantEnd.strictRight A strategy hwin fallbackLeft
    fallbackRight ((env close).inputOne, (env close).inputTwo)
  have hpairNextAtClose :
      ((.inl oneNext : OneControl A strategy hwin policy),
          (.inl twoNext : TwoControl A strategy hwin policy)) =
        profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env (close + 1) := by
    simpa
      [profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace,
        FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
        henvGraphClose, oneNext, twoNext, fresh]
      using congrArg
        (fun controls : OneControl A strategy hwin policy ×
            TwoControl A strategy hwin policy ↦
          ((profiledRawJointHybridPhysicalCompatiblePhaseLiveNoRecvOne A
              strategy hwin policy controls.1 (env close).inputOne).1,
            (profiledRawJointHybridPhysicalCompatiblePhaseLiveOpenRecvTwo A
              strategy hwin policy initialTwo fallbackLeft fallbackRight
                controls.2 (env close).inputTwo controls.1
                  (env close).inputOne).1))
        hpairClose
  have hcloseSucc : close + 1 = schedule.cutPackage.cuts (k + 2) := by
    have hpositive : 0 < schedule.cutPackage.cuts (k + 2) :=
      lt_of_le_of_lt (Nat.zero_le _) (schedule.cutPackage.cuts_strictMono
        (Nat.lt_succ_self (k + 1)))
    simp [close, Nat.sub_add_cancel (Nat.succ_le_iff.mpr hpositive)]
  have hpairNext := hpairNextAtClose
  rw [hcloseSucc] at hpairNext
  refine ⟨state, move, tableMember, row, ownerControl, monitorState, oneEnd,
    twoEnd, oneNext, twoNext, {
    invariantEnd := hinvariantEnd
    selectedEnd := ?_
    literalPrefix := ?_
    closingRecord := ?_
    invariantNext := by simpa [oneNext, twoNext] using hinvariantNext
    selectedNext := hpairNext
    successor := ⟨slot, ?_, ?_⟩ }⟩
  · simpa [close] using hpairClose
  · have hlength : close - start = length := by omega
    simpa [word, start, length, close, hlength] using hliteral
  · have hlength : close - start = length := by omega
    simpa [word, start, length, close, hlength] using hclosing
  · have hlength : close - start = length := by omega
    simpa [start, length, close, hlength] using htarget
  · have hlength : close - start = length := by omega
    simpa [start, length, close, fresh, twoNext, hlength] using hnext

/-- Left-oriented mirror of the complete strict successor lineage package. -/
structure
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftStrictSuccessorLineageAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (env : EnvironmentSequence In₁ In₂)
    (schedule : OperationalCloseMemberSchedule
      (fun j ↦
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env j).graph))
    (k : Nat)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (tableMember : Bool) (row : PairedEntryRow)
    (ownerControl : (move.memberController A false).Control)
    (monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A strategy
        hwin (initial := initial) move false).State)
    (oneEnd : OnePending A strategy hwin policy)
    (twoEnd : TwoPending A strategy hwin policy)
    (oneNext : OnePending A strategy hwin policy)
    (twoNext : TwoPending A strategy hwin policy) : Prop where
  invariantEnd :
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A strategy
      hwin policy oneEnd twoEnd
  selectedEnd :
    ((.inl oneEnd : OneControl A strategy hwin policy),
        (.inl twoEnd : TwoControl A strategy hwin policy)) =
      profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace A strategy
        hwin policy initialOne initialTwo fallbackLeft fallbackRight env
          (schedule.cutPackage.cuts (k + 2) - 1)
  literalPrefix :
    ProfiledRawJointHybridPhysicalCompatibleLeftLiteralPrefixAt A strategy
      hwin policy state move tableMember row
        (fun j ↦
          ((env (schedule.cutPackage.cuts (k + 1) + j)).inputOne,
            (env (schedule.cutPackage.cuts (k + 1) + j)).inputTwo))
        ownerControl monitorState
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env)
        (schedule.cutPackage.cuts (k + 1))
        (schedule.cutPackage.openLength (k + 1))
  closingRecord :
    profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A strategy
        hwin policy initialOne initialTwo fallbackLeft fallbackRight env
          (schedule.cutPackage.cuts (k + 2) - 1) =
      profiledRawJointTargetLeftClosingRecordForMember false row
        (profiledRawJointTargetLeftPhysicalLetter A
          (profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A strategy
            hwin policy state move tableMember
              (fun j ↦
                ((env (schedule.cutPackage.cuts (k + 1) + j)).inputOne,
                  (env (schedule.cutPackage.cuts (k + 1) + j)).inputTwo))
              (schedule.cutPackage.openLength (k + 1))))
  invariantNext :
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A strategy
      hwin policy oneNext twoNext
  selectedNext :
    ((.inl oneNext : OneControl A strategy hwin policy),
        (.inl twoNext : TwoControl A strategy hwin policy)) =
      profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace A strategy
        hwin policy initialOne initialTwo fallbackLeft fallbackRight env
          (schedule.cutPackage.cuts (k + 2))
  successor :
    ∃ slot : ProfiledRawRightSlot A,
      ProfiledRawJointHybridPhysicalCompatibleRootAlignedSuccessorTargetAt A
          strategy hwin policy state
            (((profiledRawJointHybridPhysicalCompatibleLeftDecoratedPlay A
              strategy hwin policy state move tableMember
                (fun j ↦
                  ((env (schedule.cutPackage.cuts (k + 1) + j)).inputOne,
                    (env (schedule.cutPackage.cuts (k + 1) + j)).inputTwo))
                (schedule.cutPackage.openLength (k + 1))).2.1.target row).1)
            .right (.inl slot) ∧
        oneNext.2.1.baseShared.1 =
          profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
            hwin
              (((profiledRawJointHybridPhysicalCompatibleLeftDecoratedPlay A
                strategy hwin policy state move tableMember
                  (fun j ↦
                    ((env (schedule.cutPackage.cuts (k + 1) + j)).inputOne,
                      (env (schedule.cutPackage.cuts (k + 1) + j)).inputTwo))
                  (schedule.cutPackage.openLength (k + 1))).2.1.target row).1)

/-- Every scheduled strict-left successor block has its complete lineage
package. -/
theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLive_exists_leftStrictSuccessorLineageAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackLeft : LeftOutput A strategy hwin initial)
    (fallbackRight : RightOutput A strategy hwin initial)
    (hinitial :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTableInvariant A
        strategy hwin policy initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂)
    (hsegmentInitial :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLivePhysicalSegmentInvariantAt
        A strategy hwin policy env
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
            strategy hwin policy initialOne initialTwo fallbackLeft
              fallbackRight env)
          0 initialOne initialTwo)
    (schedule : OperationalCloseMemberSchedule
      (fun j ↦
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env j).graph))
    (k : Nat)
    (hgraph :
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A strategy
        hwin policy initialOne initialTwo fallbackLeft fallbackRight env
          (schedule.cutPackage.cuts (k + 1))).graph = .left) :
    ∃ (state : CompatibleState A strategy hwin initial)
        (move : ProfiledRawJointLeftPhysicalSiblingMove A)
        (tableMember : Bool) (row : PairedEntryRow)
        (ownerControl : (move.memberController A false).Control)
        (monitorState :
          (profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A
            strategy hwin (initial := initial) move false).State)
        (oneEnd : OnePending A strategy hwin policy)
        (twoEnd : TwoPending A strategy hwin policy)
        (oneNext : OnePending A strategy hwin policy)
        (twoNext : TwoPending A strategy hwin policy),
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftStrictSuccessorLineageAt
        A strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
          env schedule k state move tableMember row ownerControl monitorState
            oneEnd twoEnd oneNext twoNext := by
  let word :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A strategy
      hwin policy initialOne initialTwo fallbackLeft fallbackRight env
  let start := schedule.cutPackage.cuts (k + 1)
  let length := schedule.cutPackage.openLength (k + 1)
  let close := schedule.cutPackage.cuts (k + 2) - 1
  obtain ⟨tableMember, oneEnd, twoEnd, hinvariantEnd, hpairEnd,
      hanchoredEnd⟩ :=
    profiledRawJointHybridPhysicalCompatiblePhaseLive_exists_leftAnchoredPhysicalSegmentAt_scheduledClose
      A strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
        hinitial env hsegmentInitial schedule k hgraph
  have hclosingIndex : start + length = close := by
    exact schedule.start_add_openLength_eq_closingIndex (k + 1)
  have hpairClose := hpairEnd
  rw [hclosingIndex] at hpairClose
  have hwordGraphClose : (word close).graph = .left := by
    have hclose := schedule.cutPackage.closing_graph_eq (k + 1)
    exact hclose.trans hgraph
  have henvGraphClose : (env close).graph = .left := by
    simpa [word,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord] using
        hwordGraphClose
  have hanchoredClose :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftAnchoredPhysicalSegmentAt
        A strategy hwin policy env word start close tableMember
          twoEnd.2.1.baseShared
            (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverForRecvOne
              A strategy hwin policy oneEnd twoEnd) := by
    simpa [word, start, length, close, hclosingIndex] using hanchoredEnd
  obtain ⟨state, move, ownerControl, row, monitorState, staged, hliteral,
      hclosing, slot, htarget, hnext⟩ :=
    hanchoredClose.exists_currentTargetAt A strategy hwin policy initialOne
      initialTwo fallbackLeft fallbackRight hinitial env start close oneEnd
        twoEnd hinvariantEnd hpairClose henvGraphClose tableMember
  let fresh :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshPair.{u, v, x, y, s,
      max u v x y s, max u v x y s, max u v x y s,
      max u v x y s} A strategy hwin policy fallbackLeft fallbackRight oneEnd
        twoEnd ((env close).inputOne, (env close).inputTwo)
  let oneNext : OnePending A strategy hwin policy := fresh.1.1.openControl
  let twoNext : TwoPending A strategy hwin policy :=
    (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveTwoPendingStep A
        strategy hwin policy) twoEnd (env close).inputTwo).1
  have hinvariantNext := hinvariantEnd.strictLeft A strategy hwin fallbackLeft
    fallbackRight ((env close).inputOne, (env close).inputTwo)
  have hpairNextAtClose :
      ((.inl oneNext : OneControl A strategy hwin policy),
          (.inl twoNext : TwoControl A strategy hwin policy)) =
        profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env (close + 1) := by
    simpa
      [profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticTrace,
        FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
        henvGraphClose, oneNext, twoNext, fresh]
      using congrArg
        (fun controls : OneControl A strategy hwin policy ×
            TwoControl A strategy hwin policy ↦
          ((profiledRawJointHybridPhysicalCompatiblePhaseLiveOpenRecvOne A
              strategy hwin policy initialOne fallbackLeft fallbackRight
                controls.1 (env close).inputOne controls.2
                  (env close).inputTwo).1,
            (profiledRawJointHybridPhysicalCompatiblePhaseLiveNoRecvTwo A
              strategy hwin policy controls.2 (env close).inputTwo).1))
        hpairClose
  have hcloseSucc : close + 1 = schedule.cutPackage.cuts (k + 2) := by
    have hpositive : 0 < schedule.cutPackage.cuts (k + 2) :=
      lt_of_le_of_lt (Nat.zero_le _) (schedule.cutPackage.cuts_strictMono
        (Nat.lt_succ_self (k + 1)))
    simp [close, Nat.sub_add_cancel (Nat.succ_le_iff.mpr hpositive)]
  have hpairNext := hpairNextAtClose
  rw [hcloseSucc] at hpairNext
  refine ⟨state, move, tableMember, row, ownerControl, monitorState, oneEnd,
    twoEnd, oneNext, twoNext, {
    invariantEnd := hinvariantEnd
    selectedEnd := ?_
    literalPrefix := ?_
    closingRecord := ?_
    invariantNext := by simpa [oneNext, twoNext] using hinvariantNext
    selectedNext := hpairNext
    successor := ⟨slot, ?_, ?_⟩ }⟩
  · simpa [close] using hpairClose
  · have hlength : close - start = length := by omega
    simpa [word, start, length, close, hlength] using hliteral
  · have hlength : close - start = length := by omega
    simpa [word, start, length, close, hlength] using hclosing
  · have hlength : close - start = length := by omega
    simpa [start, length, close, hlength] using htarget
  · have hlength : close - start = length := by omega
    simpa [start, length, close, fresh, oneNext, hlength] using hnext

/-! ## DPA-state lineage bridge -/

/-- Forget the packaged crossed root while retaining the exact right
successor-key relation needed by the scheduled transition packet. -/
theorem
    ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetAt.toRightSuccessorKeyAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {state : CompatibleState A strategy hwin initial}
    {target : ProfiledRawJointHybridPhysicalCompatibleSuccessorTarget A
      strategy hwin initial}
    {slot : ProfiledRawLeftSlot A}
    (targetAt :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetAt A strategy hwin
        policy state target .left (.inr slot)) :
    ProfiledRawJointHybridPhysicalCompatibleRightSuccessorKeyAt A strategy hwin
      policy state
        (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
          hwin target) target.1 := by
  rcases targetAt with ⟨rootAt, transition⟩
  cases rootAt with
  | right slot target_live =>
      exact ⟨slot, target_live, transition⟩

/-- Left-oriented mirror of `toRightSuccessorKeyAt`. -/
theorem
    ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetAt.toLeftSuccessorKeyAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {state : CompatibleState A strategy hwin initial}
    {target : ProfiledRawJointHybridPhysicalCompatibleSuccessorTarget A
      strategy hwin initial}
    {slot : ProfiledRawRightSlot A}
    (targetAt :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetAt A strategy hwin
        policy state target .right (.inl slot)) :
    ProfiledRawJointHybridPhysicalCompatibleLeftSuccessorKeyAt A strategy hwin
      policy state
        (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
          hwin target) target.1 := by
  rcases targetAt with ⟨rootAt, transition⟩
  cases rootAt with
  | left slot target_live =>
      exact ⟨slot, target_live, transition⟩

/-- Root-aligned right target packet as the corresponding finite key
relation. -/
theorem
    ProfiledRawJointHybridPhysicalCompatibleRootAlignedSuccessorTargetAt.toRightRootAlignedSuccessorKeyAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {state : CompatibleState A strategy hwin initial}
    {target : ProfiledRawJointHybridPhysicalCompatibleSuccessorTarget A
      strategy hwin initial}
    {slot : ProfiledRawLeftSlot A}
    (targetAt :
      ProfiledRawJointHybridPhysicalCompatibleRootAlignedSuccessorTargetAt A
        strategy hwin policy state target .left (.inr slot)) :
    ProfiledRawJointHybridPhysicalCompatibleRightRootAlignedSuccessorKeyAt A
      strategy hwin policy state
        (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
          hwin target) target.1 := by
  rcases targetAt with ⟨rootAt, transition⟩
  cases rootAt with
  | right slot target_live =>
      exact ⟨slot, target_live, transition⟩

/-- Root-aligned left target packet as the corresponding finite key
relation. -/
theorem
    ProfiledRawJointHybridPhysicalCompatibleRootAlignedSuccessorTargetAt.toLeftRootAlignedSuccessorKeyAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {state : CompatibleState A strategy hwin initial}
    {target : ProfiledRawJointHybridPhysicalCompatibleSuccessorTarget A
      strategy hwin initial}
    {slot : ProfiledRawRightSlot A}
    (targetAt :
      ProfiledRawJointHybridPhysicalCompatibleRootAlignedSuccessorTargetAt A
        strategy hwin policy state target .right (.inl slot)) :
    ProfiledRawJointHybridPhysicalCompatibleLeftRootAlignedSuccessorKeyAt A
      strategy hwin policy state
        (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
          hwin target) target.1 := by
  rcases targetAt with ⟨rootAt, transition⟩
  cases rootAt with
  | left slot target_live =>
      exact ⟨slot, target_live, transition⟩

/-- Once the actual checker state is known at the beginning of a strict-right
successor block, its complete phase-live lineage is exactly the scheduled
alignment consumed by `transitionCutPacket`.  Thus the only state equation
needed for the first block is propagated by the packet theorem to the next
cut. -/
theorem
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightStrictSuccessorLineageAt.toScheduledAlignment
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {initialOne : OnePending A strategy hwin policy}
    {initialTwo : TwoPending A strategy hwin policy}
    {fallbackLeft : LeftOutput A strategy hwin initial}
    {fallbackRight : RightOutput A strategy hwin initial}
    {env : EnvironmentSequence In₁ In₂}
    {schedule : OperationalCloseMemberSchedule
      (fun j ↦
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env j).graph)}
    {k : Nat}
    {state : CompatibleState A strategy hwin initial}
    {move : ProfiledRawJointRightPhysicalSiblingMove A}
    {tableMember : Bool} {row : PairedEntryRow}
    {ownerControl : (move.memberController A false).Control}
    {monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A strategy
        hwin (initial := initial) move false).State}
    {oneEnd oneNext : OnePending A strategy hwin policy}
    {twoEnd twoNext : TwoPending A strategy hwin policy}
    (lineage :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightStrictSuccessorLineageAt
        A strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
          env schedule k state move tableMember row ownerControl monitorState
            oneEnd twoEnd oneNext twoNext)
    (physicalState : A.State)
    (entryState :
      A.runFrom physicalState
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
            strategy hwin policy initialOne initialTwo fallbackLeft
              fallbackRight env)
          (schedule.cutPackage.cuts (k + 1)) =
        pairedCodeStateForRow A row move.1.source.1.1) :
    ProfiledRawJointHybridPhysicalCompatibleRightScheduledAlignmentAt A
      strategy hwin policy state move tableMember row
        (fun j ↦
          ((env (schedule.cutPackage.cuts (k + 1) + j)).inputTwo,
            (env (schedule.cutPackage.cuts (k + 1) + j)).inputOne))
        (schedule.cutPackage.openLength (k + 1)) physicalState
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env)
        schedule (k + 1) := by
  let word :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A strategy
      hwin policy initialOne initialTwo fallbackLeft fallbackRight env
  have hclosingGraph :
      (word (schedule.cutPackage.cuts (k + 2) - 1)).graph =
        (word (schedule.cutPackage.cuts (k + 1))).graph :=
    schedule.cutPackage.closing_graph_eq (k + 1)
  have hrecordGraph := congrArg RoundRecord.graph lineage.closingRecord
  have hclosingRight :
      (word (schedule.cutPackage.cuts (k + 2) - 1)).graph = .right := by
    cases row <;>
      simpa [word, pairedRightRecordForRow, rightRoundRecord] using hrecordGraph
  have hstartRight :
      (word (schedule.cutPackage.cuts (k + 1))).graph = .right :=
    hclosingGraph.symm.trans hclosingRight
  have hmember : schedule.closeMember (k + 1) = false :=
    (schedule.closeMember_eq_false_iff (k + 1)).mpr (by
      intro hboth
      exact Graph.noConfusion (hstartRight.symm.trans hboth))
  apply lineage.literalPrefix.toScheduledAlignment A strategy hwin rfl
  · intro _hne
    exact hstartRight
  · simpa [word] using entryState
  · apply Prod.ext
    · have hinputTwo := congrArg RoundRecord.inputTwo lineage.closingRecord
      cases row <;>
        simpa [word, pairedRightRecordForRow, rightRoundRecord] using hinputTwo
    · have hinputOne := congrArg RoundRecord.inputOne lineage.closingRecord
      cases row <;>
        simpa [word, pairedRightRecordForRow, rightRoundRecord] using hinputOne
  · rw [hmember]
    have houtputs := congrArg
      (fun record : RoundRecord In₁ In₂ Graph Out₁ Out₂ ↦
        record.outputPair) lineage.closingRecord
    simpa [word] using houtputs

/-- Strict-left mirror of the DPA-state lineage bridge. -/
theorem
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftStrictSuccessorLineageAt.toScheduledAlignment
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {initialOne : OnePending A strategy hwin policy}
    {initialTwo : TwoPending A strategy hwin policy}
    {fallbackLeft : LeftOutput A strategy hwin initial}
    {fallbackRight : RightOutput A strategy hwin initial}
    {env : EnvironmentSequence In₁ In₂}
    {schedule : OperationalCloseMemberSchedule
      (fun j ↦
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env j).graph)}
    {k : Nat}
    {state : CompatibleState A strategy hwin initial}
    {move : ProfiledRawJointLeftPhysicalSiblingMove A}
    {tableMember : Bool} {row : PairedEntryRow}
    {ownerControl : (move.memberController A false).Control}
    {monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A strategy
        hwin (initial := initial) move false).State}
    {oneEnd oneNext : OnePending A strategy hwin policy}
    {twoEnd twoNext : TwoPending A strategy hwin policy}
    (lineage :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftStrictSuccessorLineageAt
        A strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
          env schedule k state move tableMember row ownerControl monitorState
            oneEnd twoEnd oneNext twoNext)
    (physicalState : A.State)
    (entryState :
      A.runFrom physicalState
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
            strategy hwin policy initialOne initialTwo fallbackLeft
              fallbackRight env)
          (schedule.cutPackage.cuts (k + 1)) =
        pairedCodeStateForRow A row move.1.source.1.1) :
    ProfiledRawJointHybridPhysicalCompatibleLeftScheduledAlignmentAt A
      strategy hwin policy state move tableMember row
        (fun j ↦
          ((env (schedule.cutPackage.cuts (k + 1) + j)).inputOne,
            (env (schedule.cutPackage.cuts (k + 1) + j)).inputTwo))
        (schedule.cutPackage.openLength (k + 1)) physicalState
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env)
        schedule (k + 1) := by
  let word :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A strategy
      hwin policy initialOne initialTwo fallbackLeft fallbackRight env
  have hclosingGraph :
      (word (schedule.cutPackage.cuts (k + 2) - 1)).graph =
        (word (schedule.cutPackage.cuts (k + 1))).graph :=
    schedule.cutPackage.closing_graph_eq (k + 1)
  have hrecordGraph := congrArg RoundRecord.graph lineage.closingRecord
  have hclosingLeft :
      (word (schedule.cutPackage.cuts (k + 2) - 1)).graph = .left := by
    cases row <;>
      simpa [word, pairedLeftRecordForRow, leftRoundRecord] using hrecordGraph
  have hstartLeft :
      (word (schedule.cutPackage.cuts (k + 1))).graph = .left :=
    hclosingGraph.symm.trans hclosingLeft
  have hmember : schedule.closeMember (k + 1) = false :=
    (schedule.closeMember_eq_false_iff (k + 1)).mpr (by
      intro hboth
      exact Graph.noConfusion (hstartLeft.symm.trans hboth))
  apply lineage.literalPrefix.toScheduledAlignment A strategy hwin rfl
  · intro _hne
    exact hstartLeft
  · simpa [word] using entryState
  · apply Prod.ext
    · have hinputOne := congrArg RoundRecord.inputOne lineage.closingRecord
      cases row <;>
        simpa [word, pairedLeftRecordForRow, leftRoundRecord] using hinputOne
    · have hinputTwo := congrArg RoundRecord.inputTwo lineage.closingRecord
      cases row <;>
        simpa [word, pairedLeftRecordForRow, leftRoundRecord] using hinputTwo
  · rw [hmember]
    have houtputs := congrArg
      (fun record : RoundRecord In₁ In₂ Graph Out₁ Out₂ ↦
        record.outputPair) lineage.closingRecord
    simpa [word] using houtputs

/-- The right lineage plus one entry-state equation propagates both the
checker state and the literally installed crossed root to the next cut. -/
theorem
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightStrictSuccessorLineageAt.nextEntryState
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {initialOne : OnePending A strategy hwin policy}
    {initialTwo : TwoPending A strategy hwin policy}
    {fallbackLeft : LeftOutput A strategy hwin initial}
    {fallbackRight : RightOutput A strategy hwin initial}
    {env : EnvironmentSequence In₁ In₂}
    {schedule : OperationalCloseMemberSchedule
      (fun j ↦
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env j).graph)}
    {k : Nat}
    {state : CompatibleState A strategy hwin initial}
    {move : ProfiledRawJointRightPhysicalSiblingMove A}
    {tableMember : Bool} {row : PairedEntryRow}
    {ownerControl : (move.memberController A false).Control}
    {monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A strategy
        hwin (initial := initial) move false).State}
    {oneEnd oneNext : OnePending A strategy hwin policy}
    {twoEnd twoNext : TwoPending A strategy hwin policy}
    (lineage :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightStrictSuccessorLineageAt
        A strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
          env schedule k state move tableMember row ownerControl monitorState
            oneEnd twoEnd oneNext twoNext)
    (physicalState : A.State)
    (entryState :
      A.runFrom physicalState
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
            strategy hwin policy initialOne initialTwo fallbackLeft
              fallbackRight env)
          (schedule.cutPackage.cuts (k + 1)) =
        pairedCodeStateForRow A row move.1.source.1.1) :
    let localEnv : Nat → In₂ × In₁ := fun j ↦
      ((env (schedule.cutPackage.cuts (k + 1) + j)).inputTwo,
        (env (schedule.cutPackage.cuts (k + 1) + j)).inputOne)
    let output :=
      (profiledRawJointHybridPhysicalCompatibleRightDecoratedPlay A strategy
        hwin policy state move tableMember localEnv
          (schedule.cutPackage.openLength (k + 1))).2.1
    let target := (output.target row).1
    ∃ slot : ProfiledRawLeftSlot A,
      ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetAt A strategy hwin
          policy state target .left (.inr slot) ∧
        twoNext.2.1.baseShared.1 =
          profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
            hwin target ∧
        cutBlockMin
            (fun j ↦ A.priority
              (A.runFrom physicalState
                (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord
                  A strategy hwin policy initialOne initialTwo fallbackLeft
                    fallbackRight env) j))
            schedule.cutPackage.cuts
            (k + 1) =
          profiledRawJointThreadRootPriority A (.inr slot) ∧
        A.runFrom physicalState
            (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
              strategy hwin policy initialOne initialTwo fallbackLeft
                fallbackRight env)
            (schedule.cutPackage.cuts (k + 2)) =
          pairedCodeStateForRow A .first slot.1.1 := by
  dsimp only
  let word :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A strategy
      hwin policy initialOne initialTwo fallbackLeft fallbackRight env
  obtain ⟨lineageSlot, targetAt, nextKey⟩ := lineage.successor
  have keyAt :=
    (targetAt.toRightRootAlignedSuccessorKeyAt A strategy hwin).toSuccessorKeyAt
  let alignment := lineage.toScheduledAlignment A strategy hwin physicalState
    entryState
  obtain ⟨slot, _installed, packetTargetAt, blockMin, nextState⟩ :=
    alignment.transitionCutPacket (ParentShared := Unit) A strategy hwin ()
      keyAt
  have hclosingGraph :
      (word (schedule.cutPackage.cuts (k + 2) - 1)).graph =
        (word (schedule.cutPackage.cuts (k + 1))).graph :=
    schedule.cutPackage.closing_graph_eq (k + 1)
  have hrecordGraph := congrArg RoundRecord.graph lineage.closingRecord
  have hclosingRight :
      (word (schedule.cutPackage.cuts (k + 2) - 1)).graph = .right := by
    cases row <;>
      simpa [word, pairedRightRecordForRow, rightRoundRecord] using hrecordGraph
  have hstartRight :
      (word (schedule.cutPackage.cuts (k + 1))).graph = .right :=
    hclosingGraph.symm.trans hclosingRight
  have hmember : schedule.closeMember (k + 1) = false :=
    (schedule.closeMember_eq_false_iff (k + 1)).mpr (by
      intro hboth
      exact Graph.noConfusion (hstartRight.symm.trans hboth))
  rw [hmember] at packetTargetAt nextState
  refine ⟨slot, ?_, ?_, ?_, ?_⟩
  · simpa using packetTargetAt
  · exact nextKey
  · simpa using blockMin
  · simpa [word] using nextState

/-- Left-oriented mirror of `nextEntryState`. -/
theorem
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftStrictSuccessorLineageAt.nextEntryState
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {initialOne : OnePending A strategy hwin policy}
    {initialTwo : TwoPending A strategy hwin policy}
    {fallbackLeft : LeftOutput A strategy hwin initial}
    {fallbackRight : RightOutput A strategy hwin initial}
    {env : EnvironmentSequence In₁ In₂}
    {schedule : OperationalCloseMemberSchedule
      (fun j ↦
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env j).graph)}
    {k : Nat}
    {state : CompatibleState A strategy hwin initial}
    {move : ProfiledRawJointLeftPhysicalSiblingMove A}
    {tableMember : Bool} {row : PairedEntryRow}
    {ownerControl : (move.memberController A false).Control}
    {monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A strategy
        hwin (initial := initial) move false).State}
    {oneEnd oneNext : OnePending A strategy hwin policy}
    {twoEnd twoNext : TwoPending A strategy hwin policy}
    (lineage :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftStrictSuccessorLineageAt
        A strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
          env schedule k state move tableMember row ownerControl monitorState
            oneEnd twoEnd oneNext twoNext)
    (physicalState : A.State)
    (entryState :
      A.runFrom physicalState
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
            strategy hwin policy initialOne initialTwo fallbackLeft
              fallbackRight env)
          (schedule.cutPackage.cuts (k + 1)) =
        pairedCodeStateForRow A row move.1.source.1.1) :
    let localEnv : Nat → In₁ × In₂ := fun j ↦
      ((env (schedule.cutPackage.cuts (k + 1) + j)).inputOne,
        (env (schedule.cutPackage.cuts (k + 1) + j)).inputTwo)
    let output :=
      (profiledRawJointHybridPhysicalCompatibleLeftDecoratedPlay A strategy hwin
        policy state move tableMember localEnv
          (schedule.cutPackage.openLength (k + 1))).2.1
    let target := (output.target row).1
    ∃ slot : ProfiledRawRightSlot A,
      ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetAt A strategy hwin
          policy state target .right (.inl slot) ∧
        oneNext.2.1.baseShared.1 =
          profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
            hwin target ∧
        cutBlockMin
            (fun j ↦ A.priority
              (A.runFrom physicalState
                (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord
                  A strategy hwin policy initialOne initialTwo fallbackLeft
                    fallbackRight env) j))
            schedule.cutPackage.cuts
            (k + 1) =
          profiledRawJointThreadRootPriority A (.inl slot) ∧
        A.runFrom physicalState
            (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
              strategy hwin policy initialOne initialTwo fallbackLeft
                fallbackRight env)
            (schedule.cutPackage.cuts (k + 2)) =
          pairedCodeStateForRow A .first slot.1.1 := by
  dsimp only
  let word :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A strategy
      hwin policy initialOne initialTwo fallbackLeft fallbackRight env
  obtain ⟨lineageSlot, targetAt, nextKey⟩ := lineage.successor
  have keyAt :=
    (targetAt.toLeftRootAlignedSuccessorKeyAt A strategy hwin).toSuccessorKeyAt
  let alignment := lineage.toScheduledAlignment A strategy hwin physicalState
    entryState
  obtain ⟨slot, _installed, packetTargetAt, blockMin, nextState⟩ :=
    alignment.transitionCutPacket (ParentShared := Unit) A strategy hwin ()
      keyAt
  have hclosingGraph :
      (word (schedule.cutPackage.cuts (k + 2) - 1)).graph =
        (word (schedule.cutPackage.cuts (k + 1))).graph :=
    schedule.cutPackage.closing_graph_eq (k + 1)
  have hrecordGraph := congrArg RoundRecord.graph lineage.closingRecord
  have hclosingLeft :
      (word (schedule.cutPackage.cuts (k + 2) - 1)).graph = .left := by
    cases row <;>
      simpa [word, pairedLeftRecordForRow, leftRoundRecord] using hrecordGraph
  have hstartLeft :
      (word (schedule.cutPackage.cuts (k + 1))).graph = .left :=
    hclosingGraph.symm.trans hclosingLeft
  have hmember : schedule.closeMember (k + 1) = false :=
    (schedule.closeMember_eq_false_iff (k + 1)).mpr (by
      intro hboth
      exact Graph.noConfusion (hstartLeft.symm.trans hboth))
  rw [hmember] at packetTargetAt nextState
  refine ⟨slot, ?_, ?_, ?_, ?_⟩
  · simpa using packetTargetAt
  · exact nextKey
  · simpa using blockMin
  · simpa [word] using nextState

/-! ## Entry state normalized to the installed next move -/

/-- Root alignment eliminates the intermediate target slot from the right
packet: the checker state at the next cut is stated directly at the source of
the left move physically stored in process two's next owner. -/
theorem
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightStrictSuccessorLineageAt.nextMoveEntryState
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {initialOne : OnePending A strategy hwin policy}
    {initialTwo : TwoPending A strategy hwin policy}
    {fallbackLeft : LeftOutput A strategy hwin initial}
    {fallbackRight : RightOutput A strategy hwin initial}
    {env : EnvironmentSequence In₁ In₂}
    {schedule : OperationalCloseMemberSchedule
      (fun j ↦
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env j).graph)}
    {k : Nat}
    {state : CompatibleState A strategy hwin initial}
    {move : ProfiledRawJointRightPhysicalSiblingMove A}
    {tableMember : Bool} {row : PairedEntryRow}
    {ownerControl : (move.memberController A false).Control}
    {monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A strategy
        hwin (initial := initial) move false).State}
    {oneEnd oneNext : OnePending A strategy hwin policy}
    {twoEnd twoNext : TwoPending A strategy hwin policy}
    (lineage :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightStrictSuccessorLineageAt
        A strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
          env schedule k state move tableMember row ownerControl monitorState
            oneEnd twoEnd oneNext twoNext)
    (physicalState : A.State)
    (entryState :
      A.runFrom physicalState
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
            strategy hwin policy initialOne initialTwo fallbackLeft
              fallbackRight env)
          (schedule.cutPackage.cuts (k + 1)) =
        pairedCodeStateForRow A row move.1.source.1.1) :
    ∃ nextMove : ProfiledRawJointLeftPhysicalSiblingMove A,
      twoNext.2.1.baseShared.1.1.2.2 = some nextMove ∧
        cutBlockMin
            (fun j ↦ A.priority
              (A.runFrom physicalState
                (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord
                  A strategy hwin policy initialOne initialTwo fallbackLeft
                    fallbackRight env) j))
            schedule.cutPackage.cuts
            (k + 1) =
          profiledRawJointThreadRootPriority A (.inr nextMove.1.source) ∧
        A.runFrom physicalState
            (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
              strategy hwin policy initialOne initialTwo fallbackLeft
                fallbackRight env)
            (schedule.cutPackage.cuts (k + 2)) =
          pairedCodeStateForRow A .first nextMove.1.source.1.1 := by
  obtain ⟨packetSlot, packetTargetAt, nextKey, blockMin, nextState⟩ :=
    lineage.nextEntryState A strategy hwin physicalState entryState
  obtain ⟨lineageSlot, targetAt, _lineageNextKey⟩ := lineage.successor
  rcases targetAt.transition with ⟨aligned⟩
  obtain ⟨nextMove, targetMove, moveSource⟩ :=
    aligned.left_move_source A strategy hwin
  have packetLive :
      ((profiledRawJointHybridPhysicalCompatibleRightDecoratedPlay A strategy
        hwin policy state move tableMember
          (fun j ↦
            ((env (schedule.cutPackage.cuts (k + 1) + j)).inputTwo,
              (env (schedule.cutPackage.cuts (k + 1) + j)).inputOne))
          (schedule.cutPackage.openLength (k + 1))).2.1.target row).1.1.family.left
            () = some packetSlot := by
    cases packetTargetAt.root_at with
    | right _ live => exact live
  have lineageLive :
      ((profiledRawJointHybridPhysicalCompatibleRightDecoratedPlay A strategy
        hwin policy state move tableMember
          (fun j ↦
            ((env (schedule.cutPackage.cuts (k + 1) + j)).inputTwo,
              (env (schedule.cutPackage.cuts (k + 1) + j)).inputOne))
          (schedule.cutPackage.openLength (k + 1))).2.1.target row).1.1.family.left
            () = some lineageSlot := by
    cases targetAt.root_at with
    | right _ live => exact live
  have slotsEq : packetSlot = lineageSlot :=
    Option.some.inj (packetLive.symm.trans lineageLive)
  have packetSource : packetSlot = nextMove.1.source :=
    slotsEq.trans moveSource.symm
  refine ⟨nextMove, ?_, ?_, ?_⟩
  · rw [nextKey]
    exact targetMove
  · simpa [packetSource] using blockMin
  · simpa [packetSource] using nextState

/-- Left packet mirror, normalized to the installed next right move. -/
theorem
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftStrictSuccessorLineageAt.nextMoveEntryState
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {initialOne : OnePending A strategy hwin policy}
    {initialTwo : TwoPending A strategy hwin policy}
    {fallbackLeft : LeftOutput A strategy hwin initial}
    {fallbackRight : RightOutput A strategy hwin initial}
    {env : EnvironmentSequence In₁ In₂}
    {schedule : OperationalCloseMemberSchedule
      (fun j ↦
        (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
          strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
            env j).graph)}
    {k : Nat}
    {state : CompatibleState A strategy hwin initial}
    {move : ProfiledRawJointLeftPhysicalSiblingMove A}
    {tableMember : Bool} {row : PairedEntryRow}
    {ownerControl : (move.memberController A false).Control}
    {monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A strategy
        hwin (initial := initial) move false).State}
    {oneEnd oneNext : OnePending A strategy hwin policy}
    {twoEnd twoNext : TwoPending A strategy hwin policy}
    (lineage :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftStrictSuccessorLineageAt
        A strategy hwin policy initialOne initialTwo fallbackLeft fallbackRight
          env schedule k state move tableMember row ownerControl monitorState
            oneEnd twoEnd oneNext twoNext)
    (physicalState : A.State)
    (entryState :
      A.runFrom physicalState
          (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
            strategy hwin policy initialOne initialTwo fallbackLeft
              fallbackRight env)
          (schedule.cutPackage.cuts (k + 1)) =
        pairedCodeStateForRow A row move.1.source.1.1) :
    ∃ nextMove : ProfiledRawJointRightPhysicalSiblingMove A,
      oneNext.2.1.baseShared.1.1.2.1 = some nextMove ∧
        cutBlockMin
            (fun j ↦ A.priority
              (A.runFrom physicalState
                (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord
                  A strategy hwin policy initialOne initialTwo fallbackLeft
                    fallbackRight env) j))
            schedule.cutPackage.cuts
            (k + 1) =
          profiledRawJointThreadRootPriority A (.inl nextMove.1.source) ∧
        A.runFrom physicalState
            (profiledRawJointHybridPhysicalCompatiblePhaseLiveSemanticWord A
              strategy hwin policy initialOne initialTwo fallbackLeft
                fallbackRight env)
            (schedule.cutPackage.cuts (k + 2)) =
          pairedCodeStateForRow A .first nextMove.1.source.1.1 := by
  obtain ⟨packetSlot, packetTargetAt, nextKey, blockMin, nextState⟩ :=
    lineage.nextEntryState A strategy hwin physicalState entryState
  obtain ⟨lineageSlot, targetAt, _lineageNextKey⟩ := lineage.successor
  rcases targetAt.transition with ⟨aligned⟩
  obtain ⟨nextMove, targetMove, moveSource⟩ :=
    aligned.right_move_source A strategy hwin
  have packetLive :
      ((profiledRawJointHybridPhysicalCompatibleLeftDecoratedPlay A strategy
        hwin policy state move tableMember
          (fun j ↦
            ((env (schedule.cutPackage.cuts (k + 1) + j)).inputOne,
              (env (schedule.cutPackage.cuts (k + 1) + j)).inputTwo))
          (schedule.cutPackage.openLength (k + 1))).2.1.target row).1.1.family.right
            () = some packetSlot := by
    cases packetTargetAt.root_at with
    | left _ live => exact live
  have lineageLive :
      ((profiledRawJointHybridPhysicalCompatibleLeftDecoratedPlay A strategy
        hwin policy state move tableMember
          (fun j ↦
            ((env (schedule.cutPackage.cuts (k + 1) + j)).inputOne,
              (env (schedule.cutPackage.cuts (k + 1) + j)).inputTwo))
          (schedule.cutPackage.openLength (k + 1))).2.1.target row).1.1.family.right
            () = some lineageSlot := by
    cases targetAt.root_at with
    | left _ live => exact live
  have slotsEq : packetSlot = lineageSlot :=
    Option.some.inj (packetLive.symm.trans lineageLive)
  have packetSource : packetSlot = nextMove.1.source :=
    slotsEq.trans moveSource.symm
  refine ⟨nextMove, ?_, ?_, ?_⟩
  · rw [nextKey]
    exact targetMove
  · simpa [packetSource] using blockMin
  · simpa [packetSource] using nextState

end

end DetParityAutomaton

end DistributedSynthesis
