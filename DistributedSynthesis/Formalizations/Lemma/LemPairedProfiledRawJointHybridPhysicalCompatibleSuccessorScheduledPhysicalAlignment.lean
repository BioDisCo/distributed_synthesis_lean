/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenOverlayGlobalTraceSlice
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOperationalCloseMemberSchedule
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorMemberCutPacket

/-!
# Scheduled physical alignment for compatible successor cuts

The operational graph clock determines the fresh close member, the numerical
gap, and the graph component of the closing record.  This module isolates the
remaining literal trace facts and feeds them directly to the already proved
member-transition cut packets.

For each orientation, full closing-record equality is split into:

* the closing input pair;
* the two physical outputs; and
* the graph component, which is proved here from
  `OperationalCloseMemberSchedule`.

Thus the only controller-specific closing premise left by this interface is
an output-pair equation.  No executable transition is given a graph,
orientation, leader bit, strict-leader bit, history, or view.
-/

namespace DistributedSynthesis

universe u v x y s c

/-- Environment rounds are determined componentwise.  The base structure does
not currently export an `ext` theorem, so the physical-closing split records
the small reusable replacement here. -/
theorem EnvironmentRound.eq_of_components
    {In₁ : Type u} {In₂ : Type v}
    {left right : EnvironmentRound In₁ In₂}
    (hinputOne : left.inputOne = right.inputOne)
    (hinputTwo : left.inputTwo = right.inputTwo)
    (hgraph : left.graph = right.graph) :
    left = right := by
  cases left
  cases right
  simp_all

namespace OperationalCloseMemberSchedule

variable {graphs : Nat → Graph}

/-- The graph clock's open length is exactly the numerical cut gap excluding
the closing round. -/
theorem openLength_eq_cutGap
    (schedule : OperationalCloseMemberSchedule graphs) (k : Nat) :
    schedule.cutPackage.openLength k =
      schedule.cutPackage.cuts (k + 1) - schedule.cutPackage.cuts k - 1 := by
  have hstep := schedule.cutPackage.step_eq k
  omega

/-- The closing index is the start plus the open length. -/
theorem start_add_openLength_eq_closingIndex
    (schedule : OperationalCloseMemberSchedule graphs) (k : Nat) :
    schedule.cutPackage.cuts k + schedule.cutPackage.openLength k =
      schedule.cutPackage.cuts (k + 1) - 1 := by
  have hstep := schedule.cutPackage.step_eq k
  omega

end OperationalCloseMemberSchedule

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

private abbrev RightWord :=
  OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂)

/-! ## State-relative tails are the literal suffix of the global run -/

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Starting the DPA from its state at `start` on the dropped word gives
exactly the priority sequence of the original run shifted by `start`.  This
is the final bookkeeping step needed to use the state-relative cut packets in
`ResolvedMemberBoundaryAt`. -/
theorem cutBlockMin_runFrom_drop_eq_shifted_run
    (word : RightWord) (start : Nat) (cuts : Nat → Nat) (k : Nat) :
    cutBlockMin
        (fun j ↦ A.priority
          (A.runFrom (A.run word start) (OmegaWord.drop word start) j))
        cuts k =
      cutBlockMin (fun j ↦ A.priority (A.run word (start + j))) cuts k := by
  have hsequence :
      (fun j ↦ A.priority
        (A.runFrom (A.run word start) (OmegaWord.drop word start) j)) =
      (fun j ↦ A.priority (A.run word (start + j))) := by
    funext j
    exact congrArg A.priority
      (A.runFrom_drop A.initial word start j)
  rw [hsequence]

/-! ## Literal closing records: graph and input projections -/

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂]

@[simp] theorem
    profiledRawJointTargetRightClosingRecordForMember_inputOne
    (member : Bool) (row : PairedEntryRow)
    (letter : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    (profiledRawJointTargetRightClosingRecordForMember member row letter
      ).inputOne = letter.1.2 := by
  cases member <;> cases row <;> rfl

@[simp] theorem
    profiledRawJointTargetRightClosingRecordForMember_inputTwo
    (member : Bool) (row : PairedEntryRow)
    (letter : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    (profiledRawJointTargetRightClosingRecordForMember member row letter
      ).inputTwo = letter.1.1 := by
  cases member <;> cases row <;> rfl

@[simp] theorem profiledRawJointTargetRightClosingRecordForMember_graph
    (member : Bool) (row : PairedEntryRow)
    (letter : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    (profiledRawJointTargetRightClosingRecordForMember member row letter
      ).graph = if member then .both else .right := by
  cases member <;> cases row <;> rfl

@[simp] theorem profiledRawJointTargetLeftClosingRecordForMember_inputOne
    (member : Bool) (row : PairedEntryRow)
    (letter : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    (profiledRawJointTargetLeftClosingRecordForMember member row letter
      ).inputOne = letter.1.1 := by
  cases member <;> cases row <;> rfl

@[simp] theorem profiledRawJointTargetLeftClosingRecordForMember_inputTwo
    (member : Bool) (row : PairedEntryRow)
    (letter : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    (profiledRawJointTargetLeftClosingRecordForMember member row letter
      ).inputTwo = letter.1.2 := by
  cases member <;> cases row <;> rfl

@[simp] theorem profiledRawJointTargetLeftClosingRecordForMember_graph
    (member : Bool) (row : PairedEntryRow)
    (letter : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    (profiledRawJointTargetLeftClosingRecordForMember member row letter
      ).graph = if member then .both else .left := by
  cases member <;> cases row <;> rfl

end

/-! ## One scheduled right boundary -/

/-- The literal trace facts for one right-table block at an operational cut.

`closing_outputs` is intentionally only the two-output equation.  The input
pair is supplied separately, and the closing graph follows from the schedule.
For a false member, `strict_orientation` rules out accidentally interpreting
a strict-left block as a right-table block. -/
structure
    ProfiledRawJointHybridPhysicalCompatibleRightScheduledAlignmentAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (tableMember : Bool) (entryRow : PairedEntryRow)
    (localEnv : Nat → In₂ × In₁) (n : Nat)
    (physicalState : A.State) (word : RightWord)
    (schedule : OperationalCloseMemberSchedule (fun j ↦ (word j).graph))
    (k : Nat) : Prop where
  strict_orientation :
    (word (schedule.cutPackage.cuts k)).graph ≠ .both →
      (word (schedule.cutPackage.cuts k)).graph = .right
  entry_state :
    A.runFrom physicalState word (schedule.cutPackage.cuts k) =
      pairedCodeStateForRow A entryRow move.1.source.1.1
  records_length :
    (profiledRawJointTargetRightPhysicalPrefixRecords A entryRow
      (omegaPrefix
        (profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A strategy
          hwin policy state move tableMember localEnv) n)).length =
      schedule.cutPackage.openLength k
  records_eq_slice :
    omegaPrefix
        (OmegaWord.drop word (schedule.cutPackage.cuts k))
        (profiledRawJointTargetRightPhysicalPrefixRecords A entryRow
          (omegaPrefix
            (profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A
              strategy hwin policy state move tableMember localEnv) n)).length =
      profiledRawJointTargetRightPhysicalPrefixRecords A entryRow
        (omegaPrefix
          (profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A strategy
            hwin policy state move tableMember localEnv) n)
  closing_inputs :
    ((word (schedule.cutPackage.cuts (k + 1) - 1)).inputTwo,
        (word (schedule.cutPackage.cuts (k + 1) - 1)).inputOne) =
      (profiledRawJointTargetRightPhysicalLetter A
        (profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A strategy
          hwin policy state move tableMember localEnv n)).1
  closing_outputs :
    (word (schedule.cutPackage.cuts (k + 1) - 1)).outputPair =
      (profiledRawJointTargetRightClosingRecordForMember
        (schedule.closeMember k) entryRow
        (profiledRawJointTargetRightPhysicalLetter A
          (profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A strategy
            hwin policy state move tableMember localEnv n))).outputPair

namespace
    ProfiledRawJointHybridPhysicalCompatibleRightScheduledAlignmentAt

variable {initial : ProfiledRawJointCommonBaseWorld A strategy}
variable {policy : CompatiblePolicy A strategy hwin initial}
variable {state : CompatibleState A strategy hwin initial}
variable {move : ProfiledRawJointRightPhysicalSiblingMove A}
variable {tableMember : Bool} {entryRow : PairedEntryRow}
variable {localEnv : Nat → In₂ × In₁} {n : Nat}
variable {physicalState : A.State} {word : RightWord}
variable {schedule : OperationalCloseMemberSchedule (fun j ↦ (word j).graph)}
variable {k : Nat}

/-- The schedule turns the open-length field into the packet's numerical gap
equation. -/
theorem gap_length
    (alignment :
      ProfiledRawJointHybridPhysicalCompatibleRightScheduledAlignmentAt A
        strategy hwin policy state move tableMember entryRow localEnv n
          physicalState word schedule k) :
    (profiledRawJointTargetRightPhysicalPrefixRecords A entryRow
      (omegaPrefix
        (profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A strategy
          hwin policy state move tableMember localEnv) n)).length =
      schedule.cutPackage.cuts (k + 1) - schedule.cutPackage.cuts k - 1 := by
  rw [alignment.records_length]
  exact schedule.openLength_eq_cutGap k

/-- Graph timing, input timing, and the one output-pair premise assemble to
the complete closing-record equality required by the cut packet. -/
theorem closing_eq
    (alignment :
      ProfiledRawJointHybridPhysicalCompatibleRightScheduledAlignmentAt A
        strategy hwin policy state move tableMember entryRow localEnv n
          physicalState word schedule k) :
    OmegaWord.drop word (schedule.cutPackage.cuts k)
        (profiledRawJointTargetRightPhysicalPrefixRecords A entryRow
          (omegaPrefix
            (profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A
              strategy hwin policy state move tableMember localEnv) n)).length =
      profiledRawJointTargetRightClosingRecordForMember
        (schedule.closeMember k) entryRow
        (profiledRawJointTargetRightPhysicalLetter A
          (profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A strategy
            hwin policy state move tableMember localEnv n)) := by
  let block := profiledRawJointTargetRightPhysicalPrefixRecords A entryRow
    (omegaPrefix
      (profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A strategy
        hwin policy state move tableMember localEnv) n)
  let letter := profiledRawJointTargetRightPhysicalLetter A
    (profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A strategy hwin
      policy state move tableMember localEnv n)
  have hindex : schedule.cutPackage.cuts k + block.length =
      schedule.cutPackage.cuts (k + 1) - 1 := by
    rw [show block.length = schedule.cutPackage.openLength k by
      exact alignment.records_length]
    exact schedule.start_add_openLength_eq_closingIndex k
  change word (schedule.cutPackage.cuts k + block.length) = _
  rw [hindex]
  apply RoundRecord.eq_of_environment_eq_of_outputPair_eq
  · apply EnvironmentRound.eq_of_components
    · simpa [RoundRecord.environment, letter] using
        congrArg Prod.snd alignment.closing_inputs
    · simpa [RoundRecord.environment, letter] using
        congrArg Prod.fst alignment.closing_inputs
    · cases hmember : schedule.closeMember k with
      | false =>
          have hne : (word (schedule.cutPackage.cuts k)).graph ≠ .both :=
            (schedule.closeMember_eq_false_iff k).mp hmember
          have hstart := alignment.strict_orientation hne
          have hclose := schedule.cutPackage.closing_graph_eq k
          simpa only [RoundRecord.environment,
            profiledRawJointTargetRightClosingRecordForMember_graph,
            Bool.false_eq_true, if_false] using hclose.trans hstart
      | true =>
          have hstart : (word (schedule.cutPackage.cuts k)).graph = .both :=
            (schedule.closeMember_eq_true_iff k).mp hmember
          have hclose := schedule.cutPackage.closing_graph_eq k
          simpa only [RoundRecord.environment,
            profiledRawJointTargetRightClosingRecordForMember_graph,
            if_true] using hclose.trans hstart
  · exact alignment.closing_outputs

/-- The scheduled alignment feeds the complete installed right-boundary
packet.  In particular the fresh member is no longer a free hypothesis. -/
theorem transitionCutPacket
    {ParentShared : Type c} (shared : ParentShared)
    (alignment :
      ProfiledRawJointHybridPhysicalCompatibleRightScheduledAlignmentAt A
        strategy hwin policy state move tableMember entryRow localEnv n
          physicalState word schedule k)
    (hkey :
      let output :=
        (profiledRawJointHybridPhysicalCompatibleRightDecoratedPlay A strategy
          hwin policy state move tableMember localEnv n).2.1
      let target := (output.target entryRow).1
      ProfiledRawJointHybridPhysicalCompatibleRightSuccessorKeyAt A strategy
        hwin policy state
          (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A
            strategy hwin target)
          target.1) :
    let output :=
      (profiledRawJointHybridPhysicalCompatibleRightDecoratedPlay A strategy
        hwin policy state move tableMember localEnv n).2.1
    let pending :=
      profiledRawJointHybridPhysicalCompatibleRightPendingPayloadOfOutput A
        strategy hwin output entryRow
    let target :=
      profiledRawJointHybridPhysicalCompatibleRightPendingPayloadTarget A
        strategy hwin pending (schedule.closeMember k)
    let installed :=
      profiledRawJointHybridPhysicalCompatibleInstallLeftPendingMember.{u, v,
        x, y, s, c, max u v x y s} A strategy hwin policy
          (schedule.closeMember k, shared, pending)
    ∃ slot : ProfiledRawLeftSlot A,
      installed.1.1 =
          profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
            hwin target ∧
        ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetAt A strategy
          hwin policy state target .left (.inr slot) ∧
        cutBlockMin
            (fun j ↦ A.priority (A.runFrom physicalState word j))
            schedule.cutPackage.cuts k =
          profiledRawJointThreadRootPriority A (.inr slot) ∧
        A.runFrom physicalState word (schedule.cutPackage.cuts (k + 1)) =
          pairedCodeStateForRow A
            (profiledRawJointCloseRowOfMember (schedule.closeMember k))
            slot.1.1 := by
  exact
    profiledRawJointHybridPhysicalCompatibleRight_memberTransitionCutPacket
      A strategy hwin policy state shared move tableMember entryRow
        (schedule.closeMember k) localEnv n hkey physicalState word
        schedule.cutPackage.cuts k
        (schedule.cutPackage.cuts_strictMono (Nat.lt_succ_self k))
        alignment.entry_state alignment.gap_length alignment.records_eq_slice
        alignment.closing_eq

end
  ProfiledRawJointHybridPhysicalCompatibleRightScheduledAlignmentAt

/-! ## Left mirror -/

structure
    ProfiledRawJointHybridPhysicalCompatibleLeftScheduledAlignmentAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (tableMember : Bool) (entryRow : PairedEntryRow)
    (localEnv : Nat → In₁ × In₂) (n : Nat)
    (physicalState : A.State) (word : RightWord)
    (schedule : OperationalCloseMemberSchedule (fun j ↦ (word j).graph))
    (k : Nat) : Prop where
  strict_orientation :
    (word (schedule.cutPackage.cuts k)).graph ≠ .both →
      (word (schedule.cutPackage.cuts k)).graph = .left
  entry_state :
    A.runFrom physicalState word (schedule.cutPackage.cuts k) =
      pairedCodeStateForRow A entryRow move.1.source.1.1
  records_length :
    (profiledRawJointTargetLeftPhysicalPrefixRecords A entryRow
      (omegaPrefix
        (profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A strategy
          hwin policy state move tableMember localEnv) n)).length =
      schedule.cutPackage.openLength k
  records_eq_slice :
    omegaPrefix
        (OmegaWord.drop word (schedule.cutPackage.cuts k))
        (profiledRawJointTargetLeftPhysicalPrefixRecords A entryRow
          (omegaPrefix
            (profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A
              strategy hwin policy state move tableMember localEnv) n)).length =
      profiledRawJointTargetLeftPhysicalPrefixRecords A entryRow
        (omegaPrefix
          (profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A strategy
            hwin policy state move tableMember localEnv) n)
  closing_inputs :
    ((word (schedule.cutPackage.cuts (k + 1) - 1)).inputOne,
        (word (schedule.cutPackage.cuts (k + 1) - 1)).inputTwo) =
      (profiledRawJointTargetLeftPhysicalLetter A
        (profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A strategy
          hwin policy state move tableMember localEnv n)).1
  closing_outputs :
    (word (schedule.cutPackage.cuts (k + 1) - 1)).outputPair =
      (profiledRawJointTargetLeftClosingRecordForMember
        (schedule.closeMember k) entryRow
        (profiledRawJointTargetLeftPhysicalLetter A
          (profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A strategy
            hwin policy state move tableMember localEnv n))).outputPair

namespace
    ProfiledRawJointHybridPhysicalCompatibleLeftScheduledAlignmentAt

variable {initial : ProfiledRawJointCommonBaseWorld A strategy}
variable {policy : CompatiblePolicy A strategy hwin initial}
variable {state : CompatibleState A strategy hwin initial}
variable {move : ProfiledRawJointLeftPhysicalSiblingMove A}
variable {tableMember : Bool} {entryRow : PairedEntryRow}
variable {localEnv : Nat → In₁ × In₂} {n : Nat}
variable {physicalState : A.State} {word : RightWord}
variable {schedule : OperationalCloseMemberSchedule (fun j ↦ (word j).graph)}
variable {k : Nat}

theorem gap_length
    (alignment :
      ProfiledRawJointHybridPhysicalCompatibleLeftScheduledAlignmentAt A
        strategy hwin policy state move tableMember entryRow localEnv n
          physicalState word schedule k) :
    (profiledRawJointTargetLeftPhysicalPrefixRecords A entryRow
      (omegaPrefix
        (profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A strategy
          hwin policy state move tableMember localEnv) n)).length =
      schedule.cutPackage.cuts (k + 1) - schedule.cutPackage.cuts k - 1 := by
  rw [alignment.records_length]
  exact schedule.openLength_eq_cutGap k

theorem closing_eq
    (alignment :
      ProfiledRawJointHybridPhysicalCompatibleLeftScheduledAlignmentAt A
        strategy hwin policy state move tableMember entryRow localEnv n
          physicalState word schedule k) :
    OmegaWord.drop word (schedule.cutPackage.cuts k)
        (profiledRawJointTargetLeftPhysicalPrefixRecords A entryRow
          (omegaPrefix
            (profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A
              strategy hwin policy state move tableMember localEnv) n)).length =
      profiledRawJointTargetLeftClosingRecordForMember
        (schedule.closeMember k) entryRow
        (profiledRawJointTargetLeftPhysicalLetter A
          (profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A strategy
            hwin policy state move tableMember localEnv n)) := by
  let block := profiledRawJointTargetLeftPhysicalPrefixRecords A entryRow
    (omegaPrefix
      (profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A strategy
        hwin policy state move tableMember localEnv) n)
  let letter := profiledRawJointTargetLeftPhysicalLetter A
    (profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A strategy hwin
      policy state move tableMember localEnv n)
  have hindex : schedule.cutPackage.cuts k + block.length =
      schedule.cutPackage.cuts (k + 1) - 1 := by
    rw [show block.length = schedule.cutPackage.openLength k by
      exact alignment.records_length]
    exact schedule.start_add_openLength_eq_closingIndex k
  change word (schedule.cutPackage.cuts k + block.length) = _
  rw [hindex]
  apply RoundRecord.eq_of_environment_eq_of_outputPair_eq
  · apply EnvironmentRound.eq_of_components
    · simpa [RoundRecord.environment, letter] using
        congrArg Prod.fst alignment.closing_inputs
    · simpa [RoundRecord.environment, letter] using
        congrArg Prod.snd alignment.closing_inputs
    · cases hmember : schedule.closeMember k with
      | false =>
          have hne : (word (schedule.cutPackage.cuts k)).graph ≠ .both :=
            (schedule.closeMember_eq_false_iff k).mp hmember
          have hstart := alignment.strict_orientation hne
          have hclose := schedule.cutPackage.closing_graph_eq k
          simpa only [RoundRecord.environment,
            profiledRawJointTargetLeftClosingRecordForMember_graph,
            Bool.false_eq_true, if_false] using hclose.trans hstart
      | true =>
          have hstart : (word (schedule.cutPackage.cuts k)).graph = .both :=
            (schedule.closeMember_eq_true_iff k).mp hmember
          have hclose := schedule.cutPackage.closing_graph_eq k
          simpa only [RoundRecord.environment,
            profiledRawJointTargetLeftClosingRecordForMember_graph,
            if_true] using hclose.trans hstart
  · exact alignment.closing_outputs

theorem transitionCutPacket
    {ParentShared : Type c} (shared : ParentShared)
    (alignment :
      ProfiledRawJointHybridPhysicalCompatibleLeftScheduledAlignmentAt A
        strategy hwin policy state move tableMember entryRow localEnv n
          physicalState word schedule k)
    (hkey :
      let output :=
        (profiledRawJointHybridPhysicalCompatibleLeftDecoratedPlay A strategy
          hwin policy state move tableMember localEnv n).2.1
      let target := (output.target entryRow).1
      ProfiledRawJointHybridPhysicalCompatibleLeftSuccessorKeyAt A strategy
        hwin policy state
          (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A
            strategy hwin target)
          target.1) :
    let output :=
      (profiledRawJointHybridPhysicalCompatibleLeftDecoratedPlay A strategy
        hwin policy state move tableMember localEnv n).2.1
    let pending :=
      profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadOfOutput A
        strategy hwin output entryRow
    let target :=
      profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadTarget A
        strategy hwin pending (schedule.closeMember k)
    let installed :=
      profiledRawJointHybridPhysicalCompatibleInstallRightPendingMember.{u, v,
        x, y, s, c, max u v x y s} A strategy hwin policy
          (schedule.closeMember k, shared, pending)
    ∃ slot : ProfiledRawRightSlot A,
      installed.1.1 =
          profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
            hwin target ∧
        ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetAt A strategy
          hwin policy state target .right (.inl slot) ∧
        cutBlockMin
            (fun j ↦ A.priority (A.runFrom physicalState word j))
            schedule.cutPackage.cuts k =
          profiledRawJointThreadRootPriority A (.inl slot) ∧
        A.runFrom physicalState word (schedule.cutPackage.cuts (k + 1)) =
          pairedCodeStateForRow A
            (profiledRawJointCloseRowOfMember (schedule.closeMember k))
            slot.1.1 := by
  exact
    profiledRawJointHybridPhysicalCompatibleLeft_memberTransitionCutPacket
      A strategy hwin policy state shared move tableMember entryRow
        (schedule.closeMember k) localEnv n hkey physicalState word
        schedule.cutPackage.cuts k
        (schedule.cutPackage.cuts_strictMono (Nat.lt_succ_self k))
        alignment.entry_state alignment.gap_length alignment.records_eq_slice
        alignment.closing_eq

end ProfiledRawJointHybridPhysicalCompatibleLeftScheduledAlignmentAt

end

end DetParityAutomaton

end DistributedSynthesis
