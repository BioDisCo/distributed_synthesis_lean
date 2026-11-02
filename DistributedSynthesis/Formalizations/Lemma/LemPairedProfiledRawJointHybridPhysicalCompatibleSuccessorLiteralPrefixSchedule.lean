/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorLiteralPrefixReachability
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorScheduledPhysicalAlignment

/-!
# Literal compatible-table prefixes at operational cuts

This module carries the named local prefix through the literal physical word.
The invariant starts from an empty freshly installed table and appends one
actual strict-round record at a time.  At an operational close its two fields
are exactly the `records_length` and `records_eq_slice` obligations of the
scheduled-alignment packet.

All indices, words, and prefixes in this file are proof-side.  The finite
controller retains only the folds already present in its local controls.
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

/-! ## Right literal segments -/

/-- An aligned right owner/monitor pair after exactly the first `n` inputs of
`localEnv`, together with the literal physical records emitted since `start`.
-/
structure ProfiledRawJointHybridPhysicalCompatibleRightLiteralPrefixAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (tableMember : Bool) (row : PairedEntryRow)
    (localEnv : Nat → In₂ × In₁)
    (owner : (move.memberController A false).Control)
    (monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A
        strategy hwin (initial := initial) move false).State)
    (word : PhysicalWord (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂))
    (start n : Nat) : Prop where
  literal_reachable :
    ProfiledRawJointHybridPhysicalCompatibleRightLocallyReachableAt A strategy
      hwin policy state move owner monitorState (omegaPrefix localEnv n)
  records :
    omegaPrefix (OmegaWord.drop word start) n =
      profiledRawJointTargetRightPhysicalPrefixRecords A row
        (omegaPrefix
          (profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A
            strategy hwin policy state move tableMember localEnv) n)

namespace ProfiledRawJointHybridPhysicalCompatibleRightLiteralPrefixAt

/-- Fresh right installation starts at the empty literal prefix. -/
theorem initial
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (tableMember : Bool) (row : PairedEntryRow)
    (localEnv : Nat → In₂ × In₁)
    (word : PhysicalWord (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)) (start : Nat) :
    ProfiledRawJointHybridPhysicalCompatibleRightLiteralPrefixAt A strategy
      hwin policy state move tableMember row localEnv
        (move.memberController A false).initial
        (profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A
          strategy hwin (initial := initial) move false).initial word start 0 :=
  ⟨profiledRawJointHybridPhysicalCompatibleRightLocallyReachableAt_initial A
      strategy hwin policy state move,
    rfl⟩

/-- Append one literal strict-right record. -/
theorem step
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
    (hrecord : word (start + n) =
      pairedRightRecordForRow row
        (profiledRawJointTargetRightPhysicalLetter A
          (profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A
            strategy hwin policy state move tableMember localEnv n))) :
    let result :=
      profiledRawJointHybridPhysicalCompatibleRightReceiverStepFor A strategy
        hwin policy state move owner row monitorState (localEnv n)
    ProfiledRawJointHybridPhysicalCompatibleRightLiteralPrefixAt A strategy
      hwin policy state move tableMember row localEnv
        ((move.memberController A false).step owner (localEnv n).2)
        result.2.2.2.1 word start (n + 1) := by
  dsimp only
  constructor
  · simpa only [omegaPrefix_succ] using
      segment.literal_reachable.step A strategy hwin row (localEnv n)
  · rw [omegaPrefix_succ, omegaPrefix_succ, segment.records]
    simp only [OmegaWord.drop]
    rw [hrecord]
    simp [profiledRawJointTargetRightPhysicalPrefixRecords]

/-- The literal segment supplies exactly the two prefix fields expected at an
operational close. -/
theorem toScheduledAlignment
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
    {physicalState : A.State}
    {word : PhysicalWord (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {schedule : OperationalCloseMemberSchedule (fun j ↦ (word j).graph)}
    {k n : Nat}
    (segment :
      ProfiledRawJointHybridPhysicalCompatibleRightLiteralPrefixAt A strategy
        hwin policy state move tableMember row localEnv owner monitorState word
          (schedule.cutPackage.cuts k) n)
    (hn : n = schedule.cutPackage.openLength k)
    (hstrict : (word (schedule.cutPackage.cuts k)).graph ≠ .both →
      (word (schedule.cutPackage.cuts k)).graph = .right)
    (hentry : A.runFrom physicalState word (schedule.cutPackage.cuts k) =
      pairedCodeStateForRow A row move.1.source.1.1)
    (hinputs :
      ((word (schedule.cutPackage.cuts (k + 1) - 1)).inputTwo,
        (word (schedule.cutPackage.cuts (k + 1) - 1)).inputOne) =
      (profiledRawJointTargetRightPhysicalLetter A
        (profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A strategy
          hwin policy state move tableMember localEnv n)).1)
    (houtputs :
      (word (schedule.cutPackage.cuts (k + 1) - 1)).outputPair =
        (profiledRawJointTargetRightClosingRecordForMember
          (schedule.closeMember k) row
          (profiledRawJointTargetRightPhysicalLetter A
            (profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A
              strategy hwin policy state move tableMember localEnv n)
          )).outputPair) :
    ProfiledRawJointHybridPhysicalCompatibleRightScheduledAlignmentAt A
      strategy hwin policy state move tableMember row localEnv n physicalState
        word schedule k := by
  refine {
    strict_orientation := hstrict
    entry_state := hentry
    records_length := ?_
    records_eq_slice := ?_
    closing_inputs := hinputs
    closing_outputs := houtputs }
  · simpa [profiledRawJointTargetRightPhysicalPrefixRecords, omegaPrefix]
      using hn
  · have hlength :
        (profiledRawJointTargetRightPhysicalPrefixRecords A row
          (omegaPrefix
            (profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A
              strategy hwin policy state move tableMember localEnv) n)
        ).length = n := by
        simp [profiledRawJointTargetRightPhysicalPrefixRecords, omegaPrefix]
    rw [hlength]
    exact segment.records

end ProfiledRawJointHybridPhysicalCompatibleRightLiteralPrefixAt

/-! ## Left literal segments -/

structure ProfiledRawJointHybridPhysicalCompatibleLeftLiteralPrefixAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (tableMember : Bool) (row : PairedEntryRow)
    (localEnv : Nat → In₁ × In₂)
    (owner : (move.memberController A false).Control)
    (monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A strategy
        hwin (initial := initial) move false).State)
    (word : PhysicalWord (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂))
    (start n : Nat) : Prop where
  literal_reachable :
    ProfiledRawJointHybridPhysicalCompatibleLeftLocallyReachableAt A strategy
      hwin policy state move owner monitorState (omegaPrefix localEnv n)
  records :
    omegaPrefix (OmegaWord.drop word start) n =
      profiledRawJointTargetLeftPhysicalPrefixRecords A row
        (omegaPrefix
          (profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A strategy
            hwin policy state move tableMember localEnv) n)

namespace ProfiledRawJointHybridPhysicalCompatibleLeftLiteralPrefixAt

theorem initial
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (tableMember : Bool) (row : PairedEntryRow)
    (localEnv : Nat → In₁ × In₂)
    (word : PhysicalWord (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)) (start : Nat) :
    ProfiledRawJointHybridPhysicalCompatibleLeftLiteralPrefixAt A strategy hwin
      policy state move tableMember row localEnv
        (move.memberController A false).initial
        (profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A strategy
          hwin (initial := initial) move false).initial word start 0 :=
  ⟨profiledRawJointHybridPhysicalCompatibleLeftLocallyReachableAt_initial A
      strategy hwin policy state move,
    rfl⟩

theorem step
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {state : CompatibleState A strategy hwin initial}
    {move : ProfiledRawJointLeftPhysicalSiblingMove A}
    {tableMember : Bool} {row : PairedEntryRow}
    {localEnv : Nat → In₁ × In₂}
    {owner : (move.memberController A false).Control}
    {monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A strategy
        hwin (initial := initial) move false).State}
    {word : PhysicalWord (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {start n : Nat}
    (segment :
      ProfiledRawJointHybridPhysicalCompatibleLeftLiteralPrefixAt A strategy
        hwin policy state move tableMember row localEnv owner monitorState word
          start n)
    (hrecord : word (start + n) =
      pairedLeftRecordForRow row
        (profiledRawJointTargetLeftPhysicalLetter A
          (profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A strategy
            hwin policy state move tableMember localEnv n))) :
    let result :=
      profiledRawJointHybridPhysicalCompatibleLeftReceiverStepFor A strategy
        hwin policy state move owner row monitorState (localEnv n)
    ProfiledRawJointHybridPhysicalCompatibleLeftLiteralPrefixAt A strategy hwin
      policy state move tableMember row localEnv
        ((move.memberController A false).step owner (localEnv n).2)
        result.2.2.2.1 word start (n + 1) := by
  dsimp only
  constructor
  · simpa only [omegaPrefix_succ] using
      segment.literal_reachable.step A strategy hwin row (localEnv n)
  · rw [omegaPrefix_succ, omegaPrefix_succ, segment.records]
    simp only [OmegaWord.drop]
    rw [hrecord]
    simp [profiledRawJointTargetLeftPhysicalPrefixRecords]

theorem toScheduledAlignment
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {state : CompatibleState A strategy hwin initial}
    {move : ProfiledRawJointLeftPhysicalSiblingMove A}
    {tableMember : Bool} {row : PairedEntryRow}
    {localEnv : Nat → In₁ × In₂}
    {owner : (move.memberController A false).Control}
    {monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A strategy
        hwin (initial := initial) move false).State}
    {physicalState : A.State}
    {word : PhysicalWord (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {schedule : OperationalCloseMemberSchedule (fun j ↦ (word j).graph)}
    {k n : Nat}
    (segment :
      ProfiledRawJointHybridPhysicalCompatibleLeftLiteralPrefixAt A strategy
        hwin policy state move tableMember row localEnv owner monitorState word
          (schedule.cutPackage.cuts k) n)
    (hn : n = schedule.cutPackage.openLength k)
    (hstrict : (word (schedule.cutPackage.cuts k)).graph ≠ .both →
      (word (schedule.cutPackage.cuts k)).graph = .left)
    (hentry : A.runFrom physicalState word (schedule.cutPackage.cuts k) =
      pairedCodeStateForRow A row move.1.source.1.1)
    (hinputs :
      ((word (schedule.cutPackage.cuts (k + 1) - 1)).inputOne,
        (word (schedule.cutPackage.cuts (k + 1) - 1)).inputTwo) =
      (profiledRawJointTargetLeftPhysicalLetter A
        (profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A strategy
          hwin policy state move tableMember localEnv n)).1)
    (houtputs :
      (word (schedule.cutPackage.cuts (k + 1) - 1)).outputPair =
        (profiledRawJointTargetLeftClosingRecordForMember
          (schedule.closeMember k) row
          (profiledRawJointTargetLeftPhysicalLetter A
            (profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A
              strategy hwin policy state move tableMember localEnv n)
          )).outputPair) :
    ProfiledRawJointHybridPhysicalCompatibleLeftScheduledAlignmentAt A strategy
      hwin policy state move tableMember row localEnv n physicalState word
        schedule k := by
  refine {
    strict_orientation := hstrict
    entry_state := hentry
    records_length := ?_
    records_eq_slice := ?_
    closing_inputs := hinputs
    closing_outputs := houtputs }
  · simpa [profiledRawJointTargetLeftPhysicalPrefixRecords, omegaPrefix]
      using hn
  · have hlength :
        (profiledRawJointTargetLeftPhysicalPrefixRecords A row
          (omegaPrefix
            (profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A
              strategy hwin policy state move tableMember localEnv) n)
        ).length = n := by
        simp [profiledRawJointTargetLeftPhysicalPrefixRecords, omegaPrefix]
    rw [hlength]
    exact segment.records

end ProfiledRawJointHybridPhysicalCompatibleLeftLiteralPrefixAt

end

end DetParityAutomaton

end DistributedSynthesis
