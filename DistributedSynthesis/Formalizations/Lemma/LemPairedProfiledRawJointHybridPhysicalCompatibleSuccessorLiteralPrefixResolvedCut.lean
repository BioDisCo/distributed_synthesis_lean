/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorLiteralPrefixSchedule
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorWholeTraceBookkeeping

/-!
# Literal scheduled blocks produce resolved successor packets

This file is the index-shifting adapter between one exact literal scheduled
block and the whole-trace packet stream.  A block at schedule index `p + 1`
is the transition packet at stream index `p`: it starts in `state p`, installs
`state (p + 1)`, accounts for the priority minimum at `cuts (p + 1)`, and
records the DPA state at `cuts (p + 2)`.

The hypotheses below are precisely the proof-side lineage equalities that a
cut induction has to maintain.  The physical controller receives none of the
orientation, side, cut, prefix, or state witnesses.
-/

namespace DistributedSynthesis

universe u v x y s w c

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

/-! ## Right-oriented block -/

/-- All literal and lineage data for a right-oriented scheduled block at
`p + 1`.  The owner and monitor controls are existential because they are
proof-side folds of the exact prefix, not fields of the whole-trace stream. -/
structure
    ProfiledRawJointHybridPhysicalCompatibleRightLiteralSuccessorCutAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (initialSide : IndexedLineageSide)
    (states : Nat → CompatibleState A strategy hwin initial)
    (start : Nat) (cuts : Nat → Nat)
    (schedule : OperationalCloseMemberSchedule
      (fun j ↦
        ((OmegaWord.drop (G.globalMachineTraceWord outputOne outputTwo env)
          start) j).graph))
    (p : Nat) (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (tableMember : Bool) (entryRow : PairedEntryRow)
    (localEnv : Nat → In₂ × In₁) (n : Nat)
    {ParentShared : Type c} (shared : ParentShared) : Prop where
  cuts_eq : cuts = schedule.cutPackage.cuts
  source_state : states p = state
  side_after :
    profiledRawJointHybridPhysicalCompatibleSideAfter initialSide (p + 2) =
      .left
  literal_prefix :
    ∃ owner : (move.memberController A false).Control,
      ∃ monitorState :
          (profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A
            strategy hwin (initial := initial) move false).State,
        ProfiledRawJointHybridPhysicalCompatibleRightLiteralPrefixAt A strategy
          hwin policy state move tableMember entryRow localEnv owner
            monitorState
            (OmegaWord.drop (G.globalMachineTraceWord outputOne outputTwo env)
              start)
            (schedule.cutPackage.cuts (p + 1)) n
  open_length : n = schedule.cutPackage.openLength (p + 1)
  strict_orientation :
    ((OmegaWord.drop (G.globalMachineTraceWord outputOne outputTwo env) start)
        (schedule.cutPackage.cuts (p + 1))).graph ≠ .both →
      ((OmegaWord.drop (G.globalMachineTraceWord outputOne outputTwo env) start)
          (schedule.cutPackage.cuts (p + 1))).graph = .right
  entry_state :
    A.runFrom
        (A.run (G.globalMachineTraceWord outputOne outputTwo env) start)
        (OmegaWord.drop (G.globalMachineTraceWord outputOne outputTwo env)
          start)
        (schedule.cutPackage.cuts (p + 1)) =
      pairedCodeStateForRow A entryRow move.1.source.1.1
  closing_inputs :
    (((OmegaWord.drop (G.globalMachineTraceWord outputOne outputTwo env) start)
          (schedule.cutPackage.cuts (p + 2) - 1)).inputTwo,
      ((OmegaWord.drop (G.globalMachineTraceWord outputOne outputTwo env) start)
          (schedule.cutPackage.cuts (p + 2) - 1)).inputOne) =
      (profiledRawJointTargetRightPhysicalLetter A
        (profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A strategy
          hwin policy state move tableMember localEnv n)).1
  closing_outputs :
    ((OmegaWord.drop (G.globalMachineTraceWord outputOne outputTwo env) start)
        (schedule.cutPackage.cuts (p + 2) - 1)).outputPair =
      (profiledRawJointTargetRightClosingRecordForMember
        (schedule.closeMember (p + 1)) entryRow
        (profiledRawJointTargetRightPhysicalLetter A
          (profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A strategy
            hwin policy state move tableMember localEnv n))).outputPair
  successor_key :
    let output :=
      (profiledRawJointHybridPhysicalCompatibleRightDecoratedPlay A strategy
        hwin policy state move tableMember localEnv n).2.1
    let target := (output.target entryRow).1
    ProfiledRawJointHybridPhysicalCompatibleRightSuccessorKeyAt A strategy hwin
      policy state
        (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
          hwin target)
        target.1
  next_state :
    let output :=
      (profiledRawJointHybridPhysicalCompatibleRightDecoratedPlay A strategy
        hwin policy state move tableMember localEnv n).2.1
    let pending :=
      profiledRawJointHybridPhysicalCompatibleRightPendingPayloadOfOutput A
        strategy hwin output entryRow
    states (p + 1) =
      (profiledRawJointHybridPhysicalCompatibleInstallLeftPendingMember.{u, v,
        x, y, s, c, max u v x y s} A strategy hwin policy
          (schedule.closeMember (p + 1), shared, pending)).1.1

namespace
    ProfiledRawJointHybridPhysicalCompatibleRightLiteralSuccessorCutAt

variable {initial : ProfiledRawJointCommonBaseWorld A strategy}
variable {policy : CompatiblePolicy A strategy hwin initial}
variable {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
variable {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
variable {env : EnvironmentSequence In₁ In₂}
variable {initialSide : IndexedLineageSide}
variable {states : Nat → CompatibleState A strategy hwin initial}
variable {start : Nat} {cuts : Nat → Nat}
variable
  {schedule : OperationalCloseMemberSchedule
    (fun j ↦
      ((OmegaWord.drop (G.globalMachineTraceWord outputOne outputTwo env)
        start) j).graph)}
variable {p : Nat} {state : CompatibleState A strategy hwin initial}
variable {move : ProfiledRawJointRightPhysicalSiblingMove A}
variable {tableMember : Bool} {entryRow : PairedEntryRow}
variable {localEnv : Nat → In₂ × In₁} {n : Nat}
variable {ParentShared : Type c} {shared : ParentShared}

/-- The exact right block is the resolved stream packet at index `p`. -/
theorem nonemptyResolvedTransitionPacketAt
    (cut :
      ProfiledRawJointHybridPhysicalCompatibleRightLiteralSuccessorCutAt A
        strategy hwin policy G outputOne outputTwo env initialSide states start
          cuts schedule p state move tableMember entryRow localEnv n shared) :
    Nonempty
      (ProfiledRawJointHybridPhysicalCompatibleResolvedTransitionPacketAt A
        strategy hwin policy G outputOne outputTwo env initialSide states start
          cuts p) := by
  let word := G.globalMachineTraceWord outputOne outputTwo env
  let tail := OmegaWord.drop word start
  let output :=
    (profiledRawJointHybridPhysicalCompatibleRightDecoratedPlay A strategy hwin
      policy state move tableMember localEnv n).2.1
  let pending :=
    profiledRawJointHybridPhysicalCompatibleRightPendingPayloadOfOutput A
      strategy hwin output entryRow
  let target :=
    profiledRawJointHybridPhysicalCompatibleRightPendingPayloadTarget A strategy
      hwin pending (schedule.closeMember (p + 1))
  let installed :=
    profiledRawJointHybridPhysicalCompatibleInstallLeftPendingMember.{u, v, x,
      y, s, c, max u v x y s} A strategy hwin policy
        (schedule.closeMember (p + 1), shared, pending)
  rcases cut.literal_prefix with ⟨owner, monitorState, segment⟩
  have alignment := segment.toScheduledAlignment A strategy hwin
    cut.open_length cut.strict_orientation cut.entry_state cut.closing_inputs
      cut.closing_outputs
  have hpacket := alignment.transitionCutPacket A strategy hwin shared
    cut.successor_key
  change ∃ slot : ProfiledRawLeftSlot A,
      installed.1.1 =
          profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
            hwin target ∧
        ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetAt A strategy
          hwin policy state target .left (.inr slot) ∧
        cutBlockMin
            (fun j ↦ A.priority
              (A.runFrom (A.run word start) tail j))
            schedule.cutPackage.cuts (p + 1) =
          profiledRawJointThreadRootPriority A (.inr slot) ∧
        A.runFrom (A.run word start) tail
            (schedule.cutPackage.cuts (p + 2)) =
          pairedCodeStateForRow A
            (profiledRawJointCloseRowOfMember
              (schedule.closeMember (p + 1))) slot.1.1 at hpacket
  rcases hpacket with ⟨slot, hinstalled, htarget, hminimum, hnext⟩
  refine ⟨
    ProfiledRawJointHybridPhysicalCompatibleResolvedTransitionPacketAt.right
      cut.side_after (schedule.closeMember (p + 1)) target
        (profiledRawJointCloseRowOfMember (schedule.closeMember (p + 1)))
        ⟨slot, ?_, ?_, ?_, ?_⟩⟩
  · exact cut.next_state.trans hinstalled
  · rw [cut.source_state]
    exact htarget
  · rw [cut.cuts_eq]
    exact
      (cutBlockMin_runFrom_drop_eq_shifted_run A word start
        schedule.cutPackage.cuts (p + 1)).symm.trans hminimum
  · rw [cut.cuts_eq]
    change A.runFrom A.initial word
        (start + schedule.cutPackage.cuts (p + 2)) = _
    have hshift := hnext
    change
      A.runFrom (A.runFrom A.initial word start) (OmegaWord.drop word start)
          (schedule.cutPackage.cuts (p + 2)) = _ at hshift
    rw [A.runFrom_drop] at hshift
    exact hshift

/-- Choice-free callers can use `nonemptyResolvedTransitionPacketAt`; the
whole-trace successor function uses this canonical noncomputable projection. -/
noncomputable def toResolvedTransitionPacketAt
    (cut :
      ProfiledRawJointHybridPhysicalCompatibleRightLiteralSuccessorCutAt A
        strategy hwin policy G outputOne outputTwo env initialSide states start
          cuts schedule p state move tableMember entryRow localEnv n shared) :
    ProfiledRawJointHybridPhysicalCompatibleResolvedTransitionPacketAt A
      strategy hwin policy G outputOne outputTwo env initialSide states start
        cuts p :=
  Classical.choice (cut.nonemptyResolvedTransitionPacketAt A strategy hwin)

end
  ProfiledRawJointHybridPhysicalCompatibleRightLiteralSuccessorCutAt

/-! ## Left-oriented block -/

/-- Left-oriented mirror of
`ProfiledRawJointHybridPhysicalCompatibleRightLiteralSuccessorCutAt`.

The block at schedule index `p + 1` starts in `states p`, follows one exact
left literal prefix, and installs `states (p + 1)` at its checked closing
member. -/
structure
    ProfiledRawJointHybridPhysicalCompatibleLeftLiteralSuccessorCutAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (initialSide : IndexedLineageSide)
    (states : Nat → CompatibleState A strategy hwin initial)
    (start : Nat) (cuts : Nat → Nat)
    (schedule : OperationalCloseMemberSchedule
      (fun j ↦
        ((OmegaWord.drop (G.globalMachineTraceWord outputOne outputTwo env)
          start) j).graph))
    (p : Nat) (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (tableMember : Bool) (entryRow : PairedEntryRow)
    (localEnv : Nat → In₁ × In₂) (n : Nat)
    {ParentShared : Type c} (shared : ParentShared) : Prop where
  cuts_eq : cuts = schedule.cutPackage.cuts
  source_state : states p = state
  side_after :
    profiledRawJointHybridPhysicalCompatibleSideAfter initialSide (p + 2) =
      .right
  literal_prefix :
    ∃ owner : (move.memberController A false).Control,
      ∃ monitorState :
          (profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A
            strategy hwin (initial := initial) move false).State,
        ProfiledRawJointHybridPhysicalCompatibleLeftLiteralPrefixAt A strategy
          hwin policy state move tableMember entryRow localEnv owner
            monitorState
            (OmegaWord.drop (G.globalMachineTraceWord outputOne outputTwo env)
              start)
            (schedule.cutPackage.cuts (p + 1)) n
  open_length : n = schedule.cutPackage.openLength (p + 1)
  strict_orientation :
    ((OmegaWord.drop (G.globalMachineTraceWord outputOne outputTwo env) start)
        (schedule.cutPackage.cuts (p + 1))).graph ≠ .both →
      ((OmegaWord.drop (G.globalMachineTraceWord outputOne outputTwo env) start)
          (schedule.cutPackage.cuts (p + 1))).graph = .left
  entry_state :
    A.runFrom
        (A.run (G.globalMachineTraceWord outputOne outputTwo env) start)
        (OmegaWord.drop (G.globalMachineTraceWord outputOne outputTwo env)
          start)
        (schedule.cutPackage.cuts (p + 1)) =
      pairedCodeStateForRow A entryRow move.1.source.1.1
  closing_inputs :
    (((OmegaWord.drop (G.globalMachineTraceWord outputOne outputTwo env) start)
          (schedule.cutPackage.cuts (p + 2) - 1)).inputOne,
      ((OmegaWord.drop (G.globalMachineTraceWord outputOne outputTwo env) start)
          (schedule.cutPackage.cuts (p + 2) - 1)).inputTwo) =
      (profiledRawJointTargetLeftPhysicalLetter A
        (profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A strategy
          hwin policy state move tableMember localEnv n)).1
  closing_outputs :
    ((OmegaWord.drop (G.globalMachineTraceWord outputOne outputTwo env) start)
        (schedule.cutPackage.cuts (p + 2) - 1)).outputPair =
      (profiledRawJointTargetLeftClosingRecordForMember
        (schedule.closeMember (p + 1)) entryRow
        (profiledRawJointTargetLeftPhysicalLetter A
          (profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A strategy
            hwin policy state move tableMember localEnv n))).outputPair
  successor_key :
    let output :=
      (profiledRawJointHybridPhysicalCompatibleLeftDecoratedPlay A strategy
        hwin policy state move tableMember localEnv n).2.1
    let target := (output.target entryRow).1
    ProfiledRawJointHybridPhysicalCompatibleLeftSuccessorKeyAt A strategy hwin
      policy state
        (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
          hwin target)
        target.1
  next_state :
    let output :=
      (profiledRawJointHybridPhysicalCompatibleLeftDecoratedPlay A strategy
        hwin policy state move tableMember localEnv n).2.1
    let pending :=
      profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadOfOutput A
        strategy hwin output entryRow
    states (p + 1) =
      (profiledRawJointHybridPhysicalCompatibleInstallRightPendingMember.{u, v,
        x, y, s, c, max u v x y s} A strategy hwin policy
          (schedule.closeMember (p + 1), shared, pending)).1.1

namespace
    ProfiledRawJointHybridPhysicalCompatibleLeftLiteralSuccessorCutAt

variable {initial : ProfiledRawJointCommonBaseWorld A strategy}
variable {policy : CompatiblePolicy A strategy hwin initial}
variable {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
variable {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
variable {env : EnvironmentSequence In₁ In₂}
variable {initialSide : IndexedLineageSide}
variable {states : Nat → CompatibleState A strategy hwin initial}
variable {start : Nat} {cuts : Nat → Nat}
variable
  {schedule : OperationalCloseMemberSchedule
    (fun j ↦
      ((OmegaWord.drop (G.globalMachineTraceWord outputOne outputTwo env)
        start) j).graph)}
variable {p : Nat} {state : CompatibleState A strategy hwin initial}
variable {move : ProfiledRawJointLeftPhysicalSiblingMove A}
variable {tableMember : Bool} {entryRow : PairedEntryRow}
variable {localEnv : Nat → In₁ × In₂} {n : Nat}
variable {ParentShared : Type c} {shared : ParentShared}

/-- The exact left block is the resolved stream packet at index `p`. -/
theorem nonemptyResolvedTransitionPacketAt
    (cut :
      ProfiledRawJointHybridPhysicalCompatibleLeftLiteralSuccessorCutAt A
        strategy hwin policy G outputOne outputTwo env initialSide states start
          cuts schedule p state move tableMember entryRow localEnv n shared) :
    Nonempty
      (ProfiledRawJointHybridPhysicalCompatibleResolvedTransitionPacketAt A
        strategy hwin policy G outputOne outputTwo env initialSide states start
          cuts p) := by
  let word := G.globalMachineTraceWord outputOne outputTwo env
  let tail := OmegaWord.drop word start
  let output :=
    (profiledRawJointHybridPhysicalCompatibleLeftDecoratedPlay A strategy hwin
      policy state move tableMember localEnv n).2.1
  let pending :=
    profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadOfOutput A
      strategy hwin output entryRow
  let target :=
    profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadTarget A strategy
      hwin pending (schedule.closeMember (p + 1))
  let installed :=
    profiledRawJointHybridPhysicalCompatibleInstallRightPendingMember.{u, v, x,
      y, s, c, max u v x y s} A strategy hwin policy
        (schedule.closeMember (p + 1), shared, pending)
  rcases cut.literal_prefix with ⟨owner, monitorState, segment⟩
  have alignment := segment.toScheduledAlignment A strategy hwin
    cut.open_length cut.strict_orientation cut.entry_state cut.closing_inputs
      cut.closing_outputs
  have hpacket := alignment.transitionCutPacket A strategy hwin shared
    cut.successor_key
  change ∃ slot : ProfiledRawRightSlot A,
      installed.1.1 =
          profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
            hwin target ∧
        ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetAt A strategy
          hwin policy state target .right (.inl slot) ∧
        cutBlockMin
            (fun j ↦ A.priority
              (A.runFrom (A.run word start) tail j))
            schedule.cutPackage.cuts (p + 1) =
          profiledRawJointThreadRootPriority A (.inl slot) ∧
        A.runFrom (A.run word start) tail
            (schedule.cutPackage.cuts (p + 2)) =
          pairedCodeStateForRow A
            (profiledRawJointCloseRowOfMember
              (schedule.closeMember (p + 1))) slot.1.1 at hpacket
  rcases hpacket with ⟨slot, hinstalled, htarget, hminimum, hnext⟩
  refine ⟨
    ProfiledRawJointHybridPhysicalCompatibleResolvedTransitionPacketAt.left
      cut.side_after (schedule.closeMember (p + 1)) target
        (profiledRawJointCloseRowOfMember (schedule.closeMember (p + 1)))
        ⟨slot, ?_, ?_, ?_, ?_⟩⟩
  · exact cut.next_state.trans hinstalled
  · rw [cut.source_state]
    exact htarget
  · rw [cut.cuts_eq]
    exact
      (cutBlockMin_runFrom_drop_eq_shifted_run A word start
        schedule.cutPackage.cuts (p + 1)).symm.trans hminimum
  · rw [cut.cuts_eq]
    change A.runFrom A.initial word
        (start + schedule.cutPackage.cuts (p + 2)) = _
    have hshift := hnext
    change
      A.runFrom (A.runFrom A.initial word start) (OmegaWord.drop word start)
          (schedule.cutPackage.cuts (p + 2)) = _ at hshift
    rw [A.runFrom_drop] at hshift
    exact hshift

/-- Choice-free callers can use `nonemptyResolvedTransitionPacketAt`; the
whole-trace successor function uses this canonical noncomputable projection. -/
noncomputable def toResolvedTransitionPacketAt
    (cut :
      ProfiledRawJointHybridPhysicalCompatibleLeftLiteralSuccessorCutAt A
        strategy hwin policy G outputOne outputTwo env initialSide states start
          cuts schedule p state move tableMember entryRow localEnv n shared) :
    ProfiledRawJointHybridPhysicalCompatibleResolvedTransitionPacketAt A
      strategy hwin policy G outputOne outputTwo env initialSide states start
        cuts p :=
  Classical.choice (cut.nonemptyResolvedTransitionPacketAt A strategy hwin)

end
  ProfiledRawJointHybridPhysicalCompatibleLeftLiteralSuccessorCutAt

/-! ## Orientation-free successor cut -/

/-- One later scheduled block, with its orientation retained only as a
proof-side constructor.  This is the per-index object needed by the whole
trace induction: a concrete construction may choose the right or left
constructor from the graph clock without exposing that choice to either
endpoint. -/
inductive ProfiledRawJointHybridPhysicalCompatibleLiteralSuccessorCutAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (initialSide : IndexedLineageSide)
    (states : Nat → CompatibleState A strategy hwin initial)
    (start : Nat) (cuts : Nat → Nat)
    (schedule : OperationalCloseMemberSchedule
      (fun j ↦
        ((OmegaWord.drop (G.globalMachineTraceWord outputOne outputTwo env)
          start) j).graph))
    (p : Nat) : Prop where
  | right
      {state : CompatibleState A strategy hwin initial}
      {move : ProfiledRawJointRightPhysicalSiblingMove A}
      {tableMember : Bool} {entryRow : PairedEntryRow}
      {localEnv : Nat → In₂ × In₁} {n : Nat}
      {ParentShared : Type c} {shared : ParentShared}
      (cut :
        ProfiledRawJointHybridPhysicalCompatibleRightLiteralSuccessorCutAt A
          strategy hwin policy G outputOne outputTwo env initialSide states
            start cuts schedule p state move tableMember entryRow localEnv n
              shared) :
      ProfiledRawJointHybridPhysicalCompatibleLiteralSuccessorCutAt policy G
        outputOne outputTwo env initialSide states start cuts schedule p
  | left
      {state : CompatibleState A strategy hwin initial}
      {move : ProfiledRawJointLeftPhysicalSiblingMove A}
      {tableMember : Bool} {entryRow : PairedEntryRow}
      {localEnv : Nat → In₁ × In₂} {n : Nat}
      {ParentShared : Type c} {shared : ParentShared}
      (cut :
        ProfiledRawJointHybridPhysicalCompatibleLeftLiteralSuccessorCutAt A
          strategy hwin policy G outputOne outputTwo env initialSide states
            start cuts schedule p state move tableMember entryRow localEnv n
              shared) :
      ProfiledRawJointHybridPhysicalCompatibleLiteralSuccessorCutAt policy G
        outputOne outputTwo env initialSide states start cuts schedule p

namespace
    ProfiledRawJointHybridPhysicalCompatibleLiteralSuccessorCutAt

variable {initial : ProfiledRawJointCommonBaseWorld A strategy}
variable {policy : CompatiblePolicy A strategy hwin initial}
variable {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
variable {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
variable {env : EnvironmentSequence In₁ In₂}
variable {initialSide : IndexedLineageSide}
variable {states : Nat → CompatibleState A strategy hwin initial}
variable {start : Nat} {cuts : Nat → Nat}
variable
  {schedule : OperationalCloseMemberSchedule
    (fun j ↦
      ((OmegaWord.drop (G.globalMachineTraceWord outputOne outputTwo env)
        start) j).graph)}
variable {p : Nat}

/-- Erase the proof-side orientation and obtain the resolved transition packet
at the same stream index. -/
theorem nonemptyResolvedTransitionPacketAt
    (cut :
      ProfiledRawJointHybridPhysicalCompatibleLiteralSuccessorCutAt.{u, v, x,
        y, s, w, c} A strategy hwin policy G outputOne outputTwo env initialSide
          states start cuts schedule p) :
    Nonempty
      (ProfiledRawJointHybridPhysicalCompatibleResolvedTransitionPacketAt A
        strategy hwin policy G outputOne outputTwo env initialSide states start
          cuts p) := by
  cases cut with
  | right cut =>
      exact cut.nonemptyResolvedTransitionPacketAt A strategy hwin
  | left cut =>
      exact cut.nonemptyResolvedTransitionPacketAt A strategy hwin

/-- Canonical noncomputable projection used by a whole-trace successor
function. -/
noncomputable def toResolvedTransitionPacketAt
    (cut :
      ProfiledRawJointHybridPhysicalCompatibleLiteralSuccessorCutAt.{u, v, x,
        y, s, w, c} A strategy hwin policy G outputOne outputTwo env initialSide
          states start cuts schedule p) :
    ProfiledRawJointHybridPhysicalCompatibleResolvedTransitionPacketAt A
      strategy hwin policy G outputOne outputTwo env initialSide states start
        cuts p :=
  Classical.choice (cut.nonemptyResolvedTransitionPacketAt A strategy hwin)

end
  ProfiledRawJointHybridPhysicalCompatibleLiteralSuccessorCutAt

end

end DetParityAutomaton

end DistributedSynthesis
