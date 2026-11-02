/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorCarrier
import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingCanonicalFreshHandlers

/-!
# Operational receiver payload and delayed successor installation

This file specializes the generic payload of the compatible-state carrier.
For each orientation it is

`Option (Σ installedMove, PairedEntryRow × monitorState × Option receiverOutput)`.

The retained `receiverOutput` is the *whole* row-exact finite table.  The old
acknowledged table member first selects one current entry row, hence one target
and one compatible-policy key.  The independent fresh open/close member then
selects only the next receiver/DPA row (`.first` or `.both`).

The unconditional construction below stores the one selected target together
with both possible next-row receiver initializations in one common pending
payload.  Its false/true candidates share the same parent control, target,
key, and output; only the next receiver row differs.

The older same-key fork initialized at `.first` is retained under an
explicit `StrictTail` name.  It is valid after the last simultaneous close,
but is not used as an unconditional close.  No executable definition in this
file receives a graph, orientation, leader bit, strict-leader bit, history,
or view.
-/

namespace DistributedSynthesis

universe u v x y s c d

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

private abbrev SuccessorTarget
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleSuccessorTarget A strategy hwin
    initial

private abbrev RightOutput
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleSuccessorRightReceiverOutput A
    strategy hwin initial

private abbrev LeftOutput
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleSuccessorLeftReceiverOutput A
    strategy hwin initial

/-! ## Concrete finite receiver payloads -/

/-- Receiver state of a right physical table.  The last component retains
the complete row-indexed decorated output of the latest receive. -/
noncomputable abbrev
    ProfiledRawJointHybridPhysicalCompatibleRightReceiverState
    {initial : ProfiledRawJointCommonBaseWorld A strategy} :=
  Σ move : ProfiledRawJointRightPhysicalSiblingMove A,
    PairedEntryRow ×
      (profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A
        strategy hwin (initial := initial) move false).State ×
      Option (RightOutput A strategy hwin initial)

noncomputable abbrev
    ProfiledRawJointHybridPhysicalCompatibleLeftReceiverState
    {initial : ProfiledRawJointCommonBaseWorld A strategy} :=
  Σ move : ProfiledRawJointLeftPhysicalSiblingMove A,
    PairedEntryRow ×
      (profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A strategy
        hwin (initial := initial) move false).State ×
      Option (LeftOutput A strategy hwin initial)

noncomputable instance
    {initial : ProfiledRawJointCommonBaseWorld A strategy} :
    Fintype
      (ProfiledRawJointHybridPhysicalCompatibleRightReceiverState A strategy
        hwin (initial := initial)) := by
  classical
  infer_instance

noncomputable instance
    {initial : ProfiledRawJointCommonBaseWorld A strategy} :
    Fintype
      (ProfiledRawJointHybridPhysicalCompatibleLeftReceiverState A strategy
        hwin (initial := initial)) := by
  classical
  infer_instance

/-- The concrete right payload used by the acknowledged carrier. -/
noncomputable abbrev ProfiledRawJointHybridPhysicalCompatibleRightPayload
    {initial : ProfiledRawJointCommonBaseWorld A strategy} :=
  Option
    (ProfiledRawJointHybridPhysicalCompatibleRightReceiverState A strategy
      hwin (initial := initial))

/-- Left payload. -/
noncomputable abbrev ProfiledRawJointHybridPhysicalCompatibleLeftPayload
    {initial : ProfiledRawJointCommonBaseWorld A strategy} :=
  Option
    (ProfiledRawJointHybridPhysicalCompatibleLeftReceiverState A strategy hwin
      (initial := initial))

noncomputable instance
    {initial : ProfiledRawJointCommonBaseWorld A strategy} :
    Fintype
      (ProfiledRawJointHybridPhysicalCompatibleRightPayload A strategy hwin
        (initial := initial)) := by
  classical
  infer_instance

noncomputable instance
    {initial : ProfiledRawJointCommonBaseWorld A strategy} :
    Fintype
      (ProfiledRawJointHybridPhysicalCompatibleLeftPayload A strategy hwin
        (initial := initial)) := by
  classical
  infer_instance

/-- Install the right table named by a compatible key at an explicitly
selected entry row.  The row is finite pending data, not an observed graph. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleRightPayloadAtRow
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (state : CompatibleState A strategy hwin initial) (row : PairedEntryRow) :
    ProfiledRawJointHybridPhysicalCompatibleRightPayload A strategy hwin
      (initial := initial) :=
  match state.1.2.1 with
  | none => none
  | some move =>
      some ⟨move, row,
        (profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A
          strategy hwin (initial := initial) move false).initial,
        none⟩

/-- Left row-parametric install. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleLeftPayloadAtRow
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (state : CompatibleState A strategy hwin initial) (row : PairedEntryRow) :
    ProfiledRawJointHybridPhysicalCompatibleLeftPayload A strategy hwin
      (initial := initial) :=
  match state.1.2.2 with
  | none => none
  | some move =>
      some ⟨move, row,
        (profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A
          strategy hwin (initial := initial) move false).initial,
        none⟩

/-- A present right payload has exactly the requested move and row. -/
theorem profiledRawJointHybridPhysicalCompatibleRightPayloadAtRow_exact
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (hmove : state.1.2.1 = some move) (row : PairedEntryRow) :
    ∃ receiver :
        ProfiledRawJointHybridPhysicalCompatibleRightReceiverState A strategy
          hwin (initial := initial),
      profiledRawJointHybridPhysicalCompatibleRightPayloadAtRow A strategy hwin
          state row = some receiver ∧
        receiver.1 = move ∧ receiver.2.1 = row := by
  refine ⟨⟨move, row,
    (profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A strategy
      hwin (initial := initial) move false).initial, none⟩, ?_, rfl, rfl⟩
  simp [profiledRawJointHybridPhysicalCompatibleRightPayloadAtRow, hmove]

/-- Left mirror. -/
theorem profiledRawJointHybridPhysicalCompatibleLeftPayloadAtRow_exact
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hmove : state.1.2.2 = some move) (row : PairedEntryRow) :
    ∃ receiver :
        ProfiledRawJointHybridPhysicalCompatibleLeftReceiverState A strategy
          hwin (initial := initial),
      profiledRawJointHybridPhysicalCompatibleLeftPayloadAtRow A strategy hwin
          state row = some receiver ∧
        receiver.1 = move ∧ receiver.2.1 = row := by
  refine ⟨⟨move, row,
    (profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A strategy
      hwin (initial := initial) move false).initial, none⟩, ?_, rfl, rfl⟩
  simp [profiledRawJointHybridPhysicalCompatibleLeftPayloadAtRow, hmove]

/-! ## Exact receiver updates -/

/-- Advance a right receiver from the delivered owner control.  No row is an
argument: the locally retained row is preserved, and the whole row-exact
output is staged. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleRightReceiverStepFor
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (row : PairedEntryRow)
    (monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A
        strategy hwin (initial := initial) move false).State)
    (input : In₂ × In₁) :
    RightOutput A strategy hwin initial ×
      ProfiledRawJointHybridPhysicalCompatibleRightReceiverState A strategy
        hwin (initial := initial) :=
  let monitor :=
    profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A strategy
      hwin (initial := initial) move false
  let controller :=
    profiledRawJointHybridPhysicalCompatibleDecoratedRightMemberController A
      strategy hwin policy state move false
  let label := controller.labelOf owner
  let output := label.2 monitorState input
  let nextState := monitor.step monitorState
    (input, output, label.1 input.2)
  (output, ⟨move, row, nextState, some output⟩)

/-- Left receiver update. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleLeftReceiverStepFor
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (row : PairedEntryRow)
    (monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A strategy
        hwin (initial := initial) move false).State)
    (input : In₁ × In₂) :
    LeftOutput A strategy hwin initial ×
      ProfiledRawJointHybridPhysicalCompatibleLeftReceiverState A strategy
        hwin (initial := initial) :=
  let monitor :=
    profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A strategy
      hwin (initial := initial) move false
  let controller :=
    profiledRawJointHybridPhysicalCompatibleDecoratedLeftMemberController A
      strategy hwin policy state move false
  let label := controller.labelOf owner
  let output := label.2 monitorState input
  let nextState := monitor.step monitorState
    (input, output, label.1 input.2)
  (output, ⟨move, row, nextState, some output⟩)

@[simp] theorem
    profiledRawJointHybridPhysicalCompatibleRightReceiverStepFor_row
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (row : PairedEntryRow)
    (monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A strategy
        hwin (initial := initial) move false).State)
    (input : In₂ × In₁) :
    (profiledRawJointHybridPhysicalCompatibleRightReceiverStepFor A strategy
      hwin policy state move owner row monitorState input).2.2.1 = row :=
  rfl

@[simp] theorem
    profiledRawJointHybridPhysicalCompatibleRightReceiverStepFor_stage
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (row : PairedEntryRow)
    (monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A strategy
        hwin (initial := initial) move false).State)
    (input : In₂ × In₁) :
    (profiledRawJointHybridPhysicalCompatibleRightReceiverStepFor A strategy
      hwin policy state move owner row monitorState input).2.2.2.2 =
        some
          (profiledRawJointHybridPhysicalCompatibleRightReceiverStepFor A
            strategy hwin policy state move owner row monitorState input).1 :=
  rfl

@[simp] theorem
    profiledRawJointHybridPhysicalCompatibleLeftReceiverStepFor_row
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (row : PairedEntryRow)
    (monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A strategy
        hwin (initial := initial) move false).State)
    (input : In₁ × In₂) :
    (profiledRawJointHybridPhysicalCompatibleLeftReceiverStepFor A strategy
      hwin policy state move owner row monitorState input).2.2.1 = row :=
  rfl

@[simp] theorem
    profiledRawJointHybridPhysicalCompatibleLeftReceiverStepFor_stage
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (row : PairedEntryRow)
    (monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A strategy
        hwin (initial := initial) move false).State)
    (input : In₁ × In₂) :
    (profiledRawJointHybridPhysicalCompatibleLeftReceiverStepFor A strategy
      hwin policy state move owner row monitorState input).2.2.2.2 =
        some
          (profiledRawJointHybridPhysicalCompatibleLeftReceiverStepFor A
            strategy hwin policy state move owner row monitorState input).1 :=
  rfl

/-! ## Entry-selected target with two closing-row receivers

There are two independent bits at a receive boundary.

* the already acknowledged table member fixes the current block's entry row;
* the fresh open/close member fixes only the next block's receiver row.

Consequently the row-exact output is queried exactly once, at the old entry
row.  Both fresh candidates retain that one target and hence the same
compatible-policy key.  They differ only in whether the next receiver is
initialized at `.first` or `.both`.
-/

/-- Data retained by an unresolved right close.  `target` has already been
selected by the old entry row.  The fresh member selects only between the two
next-row receiver initializations. -/
structure ProfiledRawJointHybridPhysicalCompatibleRightPendingPayload
    {initial : ProfiledRawJointCommonBaseWorld A strategy} where
  target : SuccessorTarget A strategy hwin initial
  firstReceiver :
    ProfiledRawJointHybridPhysicalCompatibleLeftPayload A strategy hwin
      (initial := initial)
  bothReceiver :
    ProfiledRawJointHybridPhysicalCompatibleLeftPayload A strategy hwin
      (initial := initial)

/-- Left-close mirror. -/
structure ProfiledRawJointHybridPhysicalCompatibleLeftPendingPayload
    {initial : ProfiledRawJointCommonBaseWorld A strategy} where
  target : SuccessorTarget A strategy hwin initial
  firstReceiver :
    ProfiledRawJointHybridPhysicalCompatibleRightPayload A strategy hwin
      (initial := initial)
  bothReceiver :
    ProfiledRawJointHybridPhysicalCompatibleRightPayload A strategy hwin
      (initial := initial)

noncomputable instance
    {initial : ProfiledRawJointCommonBaseWorld A strategy} :
    Fintype
      (ProfiledRawJointHybridPhysicalCompatibleRightPendingPayload A strategy
        hwin (initial := initial)) := by
  classical
  let encode :
      ProfiledRawJointHybridPhysicalCompatibleRightPendingPayload A strategy
          hwin (initial := initial) →
        SuccessorTarget A strategy hwin initial ×
        (ProfiledRawJointHybridPhysicalCompatibleLeftPayload A strategy hwin
            (initial := initial) ×
          ProfiledRawJointHybridPhysicalCompatibleLeftPayload A strategy hwin
            (initial := initial)) :=
    fun payload ↦ (payload.target,
      (payload.firstReceiver, payload.bothReceiver))
  exact Fintype.ofInjective encode (by
    intro left right heq
    cases left
    cases right
    cases heq
    rfl)

noncomputable instance
    {initial : ProfiledRawJointCommonBaseWorld A strategy} :
    Fintype
      (ProfiledRawJointHybridPhysicalCompatibleLeftPendingPayload A strategy
        hwin (initial := initial)) := by
  classical
  let encode :
      ProfiledRawJointHybridPhysicalCompatibleLeftPendingPayload A strategy
          hwin (initial := initial) →
        SuccessorTarget A strategy hwin initial ×
        (ProfiledRawJointHybridPhysicalCompatibleRightPayload A strategy hwin
            (initial := initial) ×
          ProfiledRawJointHybridPhysicalCompatibleRightPayload A strategy hwin
            (initial := initial)) :=
    fun payload ↦ (payload.target,
      (payload.firstReceiver, payload.bothReceiver))
  exact Fintype.ofInjective encode (by
    intro left right heq
    cases left
    cases right
    cases heq
    rfl)

/-- The row represented by an acknowledged member. -/
def profiledRawJointHybridPhysicalCompatiblePendingRow
    (member : Bool) : PairedEntryRow :=
  if member then .both else .first

@[simp] theorem profiledRawJointHybridPhysicalCompatiblePendingRow_false :
    profiledRawJointHybridPhysicalCompatiblePendingRow false = .first :=
  rfl

@[simp] theorem profiledRawJointHybridPhysicalCompatiblePendingRow_true :
    profiledRawJointHybridPhysicalCompatiblePendingRow true = .both :=
  rfl

/-- Query a row-exact right output at the old entry row, then initialize the
two possible next receivers at the two fresh closing rows. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleRightPendingPayloadOfOutput
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (output : RightOutput A strategy hwin initial)
    (entryRow : PairedEntryRow) :
    ProfiledRawJointHybridPhysicalCompatibleRightPendingPayload A strategy hwin
      (initial := initial) :=
  let target := (output.target entryRow).1
  { target := target
    firstReceiver :=
      profiledRawJointHybridPhysicalCompatibleLeftPayloadAtRow A strategy hwin
        (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
          hwin target) .first
    bothReceiver :=
      profiledRawJointHybridPhysicalCompatibleLeftPayloadAtRow A strategy hwin
        (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
          hwin target) .both }

/-- Left-output mirror. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadOfOutput
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (output : LeftOutput A strategy hwin initial)
    (entryRow : PairedEntryRow) :
    ProfiledRawJointHybridPhysicalCompatibleLeftPendingPayload A strategy hwin
      (initial := initial) :=
  let target := (output.target entryRow).1
  { target := target
    firstReceiver :=
      profiledRawJointHybridPhysicalCompatibleRightPayloadAtRow A strategy hwin
        (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
          hwin target) .first
    bothReceiver :=
      profiledRawJointHybridPhysicalCompatibleRightPayloadAtRow A strategy hwin
        (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
          hwin target) .both }

def profiledRawJointHybridPhysicalCompatibleRightPendingPayloadTarget
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (payload :
      ProfiledRawJointHybridPhysicalCompatibleRightPendingPayload A strategy
        hwin (initial := initial)) (member : Bool) :
    SuccessorTarget A strategy hwin initial :=
  payload.target

def profiledRawJointHybridPhysicalCompatibleRightPendingPayloadReceiver
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (payload :
      ProfiledRawJointHybridPhysicalCompatibleRightPendingPayload A strategy
        hwin (initial := initial)) (member : Bool) :
    ProfiledRawJointHybridPhysicalCompatibleLeftPayload A strategy hwin
      (initial := initial) :=
  if member then payload.bothReceiver else payload.firstReceiver

def profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadTarget
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (payload :
      ProfiledRawJointHybridPhysicalCompatibleLeftPendingPayload A strategy
        hwin (initial := initial)) (member : Bool) :
    SuccessorTarget A strategy hwin initial :=
  payload.target

def profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadReceiver
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (payload :
      ProfiledRawJointHybridPhysicalCompatibleLeftPendingPayload A strategy
        hwin (initial := initial)) (member : Bool) :
    ProfiledRawJointHybridPhysicalCompatibleRightPayload A strategy hwin
      (initial := initial) :=
  if member then payload.bothReceiver else payload.firstReceiver

@[simp] theorem
    profiledRawJointHybridPhysicalCompatibleRightPendingPayloadOfOutput_target
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (output : RightOutput A strategy hwin initial)
    (entryRow : PairedEntryRow) (closeMember : Bool) :
    profiledRawJointHybridPhysicalCompatibleRightPendingPayloadTarget A strategy
        hwin
        (profiledRawJointHybridPhysicalCompatibleRightPendingPayloadOfOutput A
          strategy hwin output entryRow) closeMember =
      (output.target entryRow).1 := by
  rfl

@[simp] theorem
    profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadOfOutput_target
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (output : LeftOutput A strategy hwin initial)
    (entryRow : PairedEntryRow) (closeMember : Bool) :
    profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadTarget A strategy
        hwin
        (profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadOfOutput A
          strategy hwin output entryRow) closeMember =
      (output.target entryRow).1 := by
  rfl

@[simp] theorem
    profiledRawJointHybridPhysicalCompatibleRightPendingPayloadOfOutput_receiver
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (output : RightOutput A strategy hwin initial)
    (entryRow : PairedEntryRow) (closeMember : Bool) :
    profiledRawJointHybridPhysicalCompatibleRightPendingPayloadReceiver A
        strategy hwin
        (profiledRawJointHybridPhysicalCompatibleRightPendingPayloadOfOutput A
          strategy hwin output entryRow) closeMember =
      profiledRawJointHybridPhysicalCompatibleLeftPayloadAtRow A strategy hwin
        (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
          hwin
          (profiledRawJointHybridPhysicalCompatibleRightPendingPayloadTarget A
            strategy hwin
            (profiledRawJointHybridPhysicalCompatibleRightPendingPayloadOfOutput
              A strategy hwin output entryRow) closeMember))
        (profiledRawJointHybridPhysicalCompatiblePendingRow closeMember) := by
  cases closeMember <;> rfl

@[simp] theorem
    profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadOfOutput_receiver
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (output : LeftOutput A strategy hwin initial)
    (entryRow : PairedEntryRow) (closeMember : Bool) :
    profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadReceiver A
        strategy hwin
        (profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadOfOutput A
          strategy hwin output entryRow) closeMember =
      profiledRawJointHybridPhysicalCompatibleRightPayloadAtRow A strategy hwin
        (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
          hwin
          (profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadTarget A
            strategy hwin
            (profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadOfOutput
              A strategy hwin output entryRow) closeMember))
        (profiledRawJointHybridPhysicalCompatiblePendingRow closeMember) := by
  cases closeMember <;> rfl

/-- The chosen target retains the old entry row, independently of the fresh
closing member. -/
theorem
    profiledRawJointHybridPhysicalCompatibleRightPendingPayloadOfOutput_row
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (output : RightOutput A strategy hwin initial)
    (entryRow : PairedEntryRow) (closeMember : Bool) :
    profiledRawJointHybridPhysicalCompatibleSuccessorTargetRow A strategy hwin
        (profiledRawJointHybridPhysicalCompatibleRightPendingPayloadTarget A
          strategy hwin
          (profiledRawJointHybridPhysicalCompatibleRightPendingPayloadOfOutput
            A strategy hwin output entryRow) closeMember) = entryRow := by
  exact (output.target entryRow).2

theorem
    profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadOfOutput_row
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (output : LeftOutput A strategy hwin initial)
    (entryRow : PairedEntryRow) (closeMember : Bool) :
    profiledRawJointHybridPhysicalCompatibleSuccessorTargetRow A strategy hwin
        (profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadTarget A
          strategy hwin
          (profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadOfOutput A
            strategy hwin output entryRow) closeMember) = entryRow := by
  exact (output.target entryRow).2

/-! ## Same-parent unresolved fork -/

/-- The unconditional fork keeps one parent shared control and the whole
two-row payload. -/
def profiledRawJointHybridPhysicalCompatibleRightPendingFork
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {ParentShared : Type c} (shared : ParentShared)
    (payload :
      ProfiledRawJointHybridPhysicalCompatibleRightPendingPayload A strategy
        hwin (initial := initial)) :
    FiniteDelayedFork
      (FiniteAcknowledgedDelayedCarrier.DeferredMemberControl ParentShared
        (ProfiledRawJointHybridPhysicalCompatibleRightPendingPayload A strategy
          hwin (initial := initial))) :=
  FiniteAcknowledgedDelayedCarrier.deferredMemberFork shared payload

def profiledRawJointHybridPhysicalCompatibleLeftPendingFork
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {ParentShared : Type c} (shared : ParentShared)
    (payload :
      ProfiledRawJointHybridPhysicalCompatibleLeftPendingPayload A strategy
        hwin (initial := initial)) :
    FiniteDelayedFork
      (FiniteAcknowledgedDelayedCarrier.DeferredMemberControl ParentShared
        (ProfiledRawJointHybridPhysicalCompatibleLeftPendingPayload A strategy
          hwin (initial := initial))) :=
  FiniteAcknowledgedDelayedCarrier.deferredMemberFork shared payload

@[simp] theorem
    profiledRawJointHybridPhysicalCompatibleRightPendingFork_candidate
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {ParentShared : Type c} (shared : ParentShared)
    (payload :
      ProfiledRawJointHybridPhysicalCompatibleRightPendingPayload A strategy
        hwin (initial := initial)) (member : Bool) :
    (profiledRawJointHybridPhysicalCompatibleRightPendingFork A strategy hwin
      shared payload).candidate member = (member, shared, payload) := by
  exact FiniteAcknowledgedDelayedCarrier.deferredMemberFork_candidate _ _ _

@[simp] theorem
    profiledRawJointHybridPhysicalCompatibleLeftPendingFork_candidate
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {ParentShared : Type c} (shared : ParentShared)
    (payload :
      ProfiledRawJointHybridPhysicalCompatibleLeftPendingPayload A strategy
        hwin (initial := initial)) (member : Bool) :
    (profiledRawJointHybridPhysicalCompatibleLeftPendingFork A strategy hwin
      shared payload).candidate member = (member, shared, payload) := by
  exact FiniteAcknowledgedDelayedCarrier.deferredMemberFork_candidate _ _ _

/-- Arbitrary blind parent depth is safe: the child keys are inert payload
until an acknowledgement resolves the member. -/
theorem
    profiledRawJointHybridPhysicalCompatibleRightPendingFork_noRecv_coherent
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {ParentShared : Type c} {Input : Type d} {Output : Type p}
    (step : Bool → ParentShared → Input → ParentShared × Output)
    (laws : FiniteAcknowledgedDelayedCarrier.DeferredMemberStepLaws step)
    (shared : ParentShared)
    (payload :
      ProfiledRawJointHybridPhysicalCompatibleRightPendingPayload A strategy
        hwin (initial := initial)) (input : Input) :
    (profiledRawJointHybridPhysicalCompatibleRightPendingFork A strategy hwin
      shared payload).NoRecvMealyOutputCoherent
        (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv step) input :=
  FiniteAcknowledgedDelayedCarrier.deferredMemberFork_noRecvOutputCoherent
    step laws shared payload input

theorem
    profiledRawJointHybridPhysicalCompatibleLeftPendingFork_noRecv_coherent
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {ParentShared : Type c} {Input : Type d} {Output : Type p}
    (step : Bool → ParentShared → Input → ParentShared × Output)
    (laws : FiniteAcknowledgedDelayedCarrier.DeferredMemberStepLaws step)
    (shared : ParentShared)
    (payload :
      ProfiledRawJointHybridPhysicalCompatibleLeftPendingPayload A strategy
        hwin (initial := initial)) (input : Input) :
    (profiledRawJointHybridPhysicalCompatibleLeftPendingFork A strategy hwin
      shared payload).NoRecvMealyOutputCoherent
        (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv step) input :=
  FiniteAcknowledgedDelayedCarrier.deferredMemberFork_noRecvOutputCoherent
    step laws shared payload input

/-! ## Acknowledged member installation -/

/-- After the old bit is resolved, install the selected left child key and
its correspondingly row-initialized receiver. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleInstallLeftPendingMember
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    {ParentShared : Type c}
    (pending : FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
      ParentShared
        (ProfiledRawJointHybridPhysicalCompatibleRightPendingPayload A strategy
          hwin (initial := initial))) :
    ProfiledRawJointHybridPhysicalCompatibleLeftDeferredControl A strategy hwin
      policy
      (ProfiledRawJointHybridPhysicalCompatibleLeftPayload A strategy hwin
        (initial := initial)) :=
  let target :=
    profiledRawJointHybridPhysicalCompatibleRightPendingPayloadTarget A strategy
      hwin pending.2.2 pending.1
  ((⟨profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy hwin
      target,
    pending.1,
    profiledRawJointHybridPhysicalCompatibleLeftSharedInitial A strategy hwin
      policy
      (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
        hwin target)⟩),
    profiledRawJointHybridPhysicalCompatibleRightPendingPayloadReceiver A
      strategy hwin pending.2.2 pending.1)

/-- Left-close mirror. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleInstallRightPendingMember
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    {ParentShared : Type c}
    (pending : FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
      ParentShared
        (ProfiledRawJointHybridPhysicalCompatibleLeftPendingPayload A strategy
          hwin (initial := initial))) :
    ProfiledRawJointHybridPhysicalCompatibleRightDeferredControl A strategy
      hwin policy
      (ProfiledRawJointHybridPhysicalCompatibleRightPayload A strategy hwin
        (initial := initial)) :=
  let target :=
    profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadTarget A strategy
      hwin pending.2.2 pending.1
  ((⟨profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy hwin
      target,
    pending.1,
    profiledRawJointHybridPhysicalCompatibleRightSharedInitial A strategy hwin
      policy
      (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
        hwin target)⟩),
    profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadReceiver A
      strategy hwin pending.2.2 pending.1)

@[simp] theorem
    profiledRawJointHybridPhysicalCompatibleInstallLeftPendingMember_key
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    {ParentShared : Type c}
    (pending : FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
      ParentShared
        (ProfiledRawJointHybridPhysicalCompatibleRightPendingPayload A strategy
          hwin (initial := initial))) :
    (profiledRawJointHybridPhysicalCompatibleInstallLeftPendingMember A
      strategy hwin policy pending).1.1 =
      profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy hwin
        (profiledRawJointHybridPhysicalCompatibleRightPendingPayloadTarget A
          strategy hwin pending.2.2 pending.1) :=
  rfl

@[simp] theorem
    profiledRawJointHybridPhysicalCompatibleInstallRightPendingMember_key
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    {ParentShared : Type c}
    (pending : FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
      ParentShared
        (ProfiledRawJointHybridPhysicalCompatibleLeftPendingPayload A strategy
          hwin (initial := initial))) :
    (profiledRawJointHybridPhysicalCompatibleInstallRightPendingMember A
      strategy hwin policy pending).1.1 =
      profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy hwin
        (profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadTarget A
          strategy hwin pending.2.2 pending.1) :=
  rfl

/-- At an output-generated right boundary, resolution installs exactly the
row-specific opposite receiver payload. -/
theorem
    profiledRawJointHybridPhysicalCompatibleInstallLeftOfOutput_payload
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    {ParentShared : Type c} (shared : ParentShared)
    (output : RightOutput A strategy hwin initial)
    (entryRow : PairedEntryRow) (closeMember : Bool) :
    (profiledRawJointHybridPhysicalCompatibleInstallLeftPendingMember A
      strategy hwin policy
      (closeMember, shared,
        profiledRawJointHybridPhysicalCompatibleRightPendingPayloadOfOutput A
          strategy hwin output entryRow)).2 =
      profiledRawJointHybridPhysicalCompatibleLeftPayloadAtRow A strategy hwin
        (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
          hwin (output.target entryRow).1)
        (profiledRawJointHybridPhysicalCompatiblePendingRow closeMember) := by
  cases closeMember <;> rfl

theorem
    profiledRawJointHybridPhysicalCompatibleInstallRightOfOutput_payload
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    {ParentShared : Type c} (shared : ParentShared)
    (output : LeftOutput A strategy hwin initial)
    (entryRow : PairedEntryRow) (closeMember : Bool) :
    (profiledRawJointHybridPhysicalCompatibleInstallRightPendingMember A
      strategy hwin policy
      (closeMember, shared,
        profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadOfOutput A
          strategy hwin output entryRow)).2 =
      profiledRawJointHybridPhysicalCompatibleRightPayloadAtRow A strategy hwin
        (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
          hwin (output.target entryRow).1)
        (profiledRawJointHybridPhysicalCompatiblePendingRow closeMember) := by
  cases closeMember <;> rfl

/-! ## Entry-row-parametric same-policy transition audit -/

/-- The arbitrary-row successor-decoration theorem specializes directly to
the old entry row.  The fresh closing member does not alter this key. -/
theorem
    profiledRawJointHybridPhysicalCompatibleRightPendingPayloadOfDecoratedOutput_key
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (hreachable : ProfiledRawJointHybridPhysicalCompatibleReachable A strategy
      hwin initial policy state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (current_code : state.1.1 = .oneSided currentCode)
    (currentRoot : ProfiledRawJointThreadRoot A)
    (current_live :
      profiledRawJointHybridCurrentSlots A .right state.1.1 () =
        some currentRoot)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (move_eq : state.1.2.1 = some move)
    (output : ProfiledRawJointTargetRightReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂)
      (ProfiledRawJointIncidenceCode A (I := Unit)))
    (entryRow : PairedEntryRow) (closeMember : Bool)
    (target_allowed : profiledRawJointRightPhysicalSiblingAllowed A move.1
      (output.target entryRow))
    (slot : ProfiledRawLeftSlot A)
    (target_live :
      (output.target entryRow).family.left () = some slot) :
    let decorated :=
      profiledRawJointHybridPhysicalCompatibleDecorateRightReceiverOutput A
        strategy hwin policy state output
    let payload :=
      profiledRawJointHybridPhysicalCompatibleRightPendingPayloadOfOutput A
        strategy hwin decorated entryRow
    let target :=
      profiledRawJointHybridPhysicalCompatibleRightPendingPayloadTarget A
        strategy hwin payload closeMember
    ProfiledRawJointHybridPhysicalCompatibleRightRootAlignedSuccessorKeyAt A
      strategy hwin policy state
        (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
          hwin target)
        target.1 := by
  dsimp only
  simpa only
    [profiledRawJointHybridPhysicalCompatibleRightPendingPayloadOfOutput_target]
    using
      (profiledRawJointHybridPhysicalCompatibleDecorateRightReceiverOutput_key
        A strategy hwin policy state hreachable currentCode current_code
        currentRoot current_live move move_eq output
        entryRow
        target_allowed slot target_live)

/-- Left mirror. -/
theorem
    profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadOfDecoratedOutput_key
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (hreachable : ProfiledRawJointHybridPhysicalCompatibleReachable A strategy
      hwin initial policy state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (current_code : state.1.1 = .oneSided currentCode)
    (currentRoot : ProfiledRawJointThreadRoot A)
    (current_live :
      profiledRawJointHybridCurrentSlots A .left state.1.1 () =
        some currentRoot)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (move_eq : state.1.2.2 = some move)
    (output : ProfiledRawJointTargetLeftReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂)
      (ProfiledRawJointIncidenceCode A (I := Unit)))
    (entryRow : PairedEntryRow) (closeMember : Bool)
    (target_allowed : profiledRawJointLeftPhysicalSiblingAllowed A move.1
      (output.target entryRow))
    (slot : ProfiledRawRightSlot A)
    (target_live :
      (output.target entryRow).family.right () = some slot) :
    let decorated :=
      profiledRawJointHybridPhysicalCompatibleDecorateLeftReceiverOutput A
        strategy hwin policy state output
    let payload :=
      profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadOfOutput A
        strategy hwin decorated entryRow
    let target :=
      profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadTarget A
        strategy hwin payload closeMember
    ProfiledRawJointHybridPhysicalCompatibleLeftRootAlignedSuccessorKeyAt A
      strategy hwin policy state
        (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
          hwin target)
        target.1 := by
  dsimp only
  simpa only
    [profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadOfOutput_target]
    using
      (profiledRawJointHybridPhysicalCompatibleDecorateLeftReceiverOutput_key
        A strategy hwin policy state hreachable currentCode current_code
        currentRoot current_live move move_eq output
        entryRow
        target_allowed slot target_live)

/-- The selected right member therefore supplies a complete crossed-root and
same-policy transition packet, uniformly for `false` and `true`. -/
theorem
    exists_profiledRawJointHybridPhysicalCompatibleRightPendingPayloadOfDecoratedOutput_targetAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (hreachable : ProfiledRawJointHybridPhysicalCompatibleReachable A strategy
      hwin initial policy state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (current_code : state.1.1 = .oneSided currentCode)
    (currentRoot : ProfiledRawJointThreadRoot A)
    (current_live :
      profiledRawJointHybridCurrentSlots A .right state.1.1 () =
        some currentRoot)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (move_eq : state.1.2.1 = some move)
    (output : ProfiledRawJointTargetRightReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂)
      (ProfiledRawJointIncidenceCode A (I := Unit)))
    (entryRow : PairedEntryRow) (closeMember : Bool)
    (target_allowed : profiledRawJointRightPhysicalSiblingAllowed A move.1
      (output.target entryRow))
    (slot : ProfiledRawLeftSlot A)
    (target_live :
      (output.target entryRow).family.left () = some slot) :
    let decorated :=
      profiledRawJointHybridPhysicalCompatibleDecorateRightReceiverOutput A
        strategy hwin policy state output
    let payload :=
      profiledRawJointHybridPhysicalCompatibleRightPendingPayloadOfOutput A
        strategy hwin decorated entryRow
    let target :=
      profiledRawJointHybridPhysicalCompatibleRightPendingPayloadTarget A
        strategy hwin payload closeMember
    ∃ targetSlot : ProfiledRawLeftSlot A,
      ProfiledRawJointHybridPhysicalCompatibleRootAlignedSuccessorTargetAt A
        strategy hwin policy state target .left (.inr targetSlot) := by
  dsimp only
  apply
    exists_profiledRawJointHybridPhysicalCompatibleRootAlignedSuccessorTargetAt_of_rightKeyAt
      A strategy hwin policy state
  exact
    profiledRawJointHybridPhysicalCompatibleRightPendingPayloadOfDecoratedOutput_key
      A strategy hwin policy state hreachable currentCode current_code
      currentRoot current_live move move_eq output entryRow closeMember
      target_allowed slot target_live

/-- Left complete target packet. -/
theorem
    exists_profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadOfDecoratedOutput_targetAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (hreachable : ProfiledRawJointHybridPhysicalCompatibleReachable A strategy
      hwin initial policy state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (current_code : state.1.1 = .oneSided currentCode)
    (currentRoot : ProfiledRawJointThreadRoot A)
    (current_live :
      profiledRawJointHybridCurrentSlots A .left state.1.1 () =
        some currentRoot)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (move_eq : state.1.2.2 = some move)
    (output : ProfiledRawJointTargetLeftReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂)
      (ProfiledRawJointIncidenceCode A (I := Unit)))
    (entryRow : PairedEntryRow) (closeMember : Bool)
    (target_allowed : profiledRawJointLeftPhysicalSiblingAllowed A move.1
      (output.target entryRow))
    (slot : ProfiledRawRightSlot A)
    (target_live :
      (output.target entryRow).family.right () = some slot) :
    let decorated :=
      profiledRawJointHybridPhysicalCompatibleDecorateLeftReceiverOutput A
        strategy hwin policy state output
    let payload :=
      profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadOfOutput A
        strategy hwin decorated entryRow
    let target :=
      profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadTarget A
        strategy hwin payload closeMember
    ∃ targetSlot : ProfiledRawRightSlot A,
      ProfiledRawJointHybridPhysicalCompatibleRootAlignedSuccessorTargetAt A
        strategy hwin policy state target .right (.inl targetSlot) := by
  dsimp only
  apply
    exists_profiledRawJointHybridPhysicalCompatibleRootAlignedSuccessorTargetAt_of_leftKeyAt
      A strategy hwin policy state
  exact
    profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadOfDecoratedOutput_key
      A strategy hwin policy state hreachable currentCode current_code
      currentRoot current_live move move_eq output entryRow closeMember
      target_allowed slot target_live

/-! ## Strict-tail same-key specialization

The following archived draft attempted immediate child reforking.  That is
sound only after the last simultaneous close.  It is kept temporarily as a
record of the tail specialization, but is excluded from the unconditional
module until renamed and connected to an explicit persistent-tail premise.
-/

/-
/-! ## Specialized fresh forks -/

/-- Right fork with its concrete receiver payload. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleRightOperationalForkAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial) :=
  profiledRawJointHybridPhysicalCompatibleRightForkAt A strategy hwin policy
    state
    (profiledRawJointHybridPhysicalCompatibleRightPayloadAt A strategy hwin
      state)

/-- Left operational fork. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleLeftOperationalForkAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial) :=
  profiledRawJointHybridPhysicalCompatibleLeftForkAt A strategy hwin policy
    state
    (profiledRawJointHybridPhysicalCompatibleLeftPayloadAt A strategy hwin
      state)

/-- Every candidate of a live right operational fork has the named key,
installed table, and receiver row `.first`. -/
theorem
    profiledRawJointHybridPhysicalCompatibleRightOperationalForkAt_exact
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (hmove : state.1.2.1 = some move) (member : Bool) :
    let candidate :=
      (profiledRawJointHybridPhysicalCompatibleRightOperationalForkAt A
        strategy hwin policy state).candidate member
    candidate.1.1 = state ∧
      (∃ receiver :
          ProfiledRawJointHybridPhysicalCompatibleRightReceiverState A
            strategy hwin (initial := initial),
        candidate.2 = some receiver ∧ receiver.1 = move ∧
          receiver.2.1 = .first) := by
  dsimp only
  constructor
  · exact profiledRawJointHybridPhysicalCompatibleRightForkAt_key A strategy
      hwin policy state
        (profiledRawJointHybridPhysicalCompatibleRightPayloadAt A strategy hwin
          state)
        member
  · obtain ⟨receiver, hpayload, hrow⟩ :=
      profiledRawJointHybridPhysicalCompatibleRightPayloadAt_row A strategy
        hwin state move hmove
    exact ⟨receiver, by simpa
      [profiledRawJointHybridPhysicalCompatibleRightOperationalForkAt,
        profiledRawJointHybridPhysicalCompatibleRightForkAt,
        FiniteAcknowledgedDelayedCarrier.keyedDeferredMemberFork,
        FiniteDelayedFork.candidate] using hpayload.symm, by
          simpa [receiver] using rfl, hrow⟩

/-- Left mirror. -/
theorem
    profiledRawJointHybridPhysicalCompatibleLeftOperationalForkAt_exact
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hmove : state.1.2.2 = some move) (member : Bool) :
    let candidate :=
      (profiledRawJointHybridPhysicalCompatibleLeftOperationalForkAt A strategy
        hwin policy state).candidate member
    candidate.1.1 = state ∧
      (∃ receiver :
          ProfiledRawJointHybridPhysicalCompatibleLeftReceiverState A strategy
            hwin (initial := initial),
        candidate.2 = some receiver ∧ receiver.1 = move ∧
          receiver.2.1 = .first) := by
  dsimp only
  constructor
  · exact profiledRawJointHybridPhysicalCompatibleLeftForkAt_key A strategy
      hwin policy state
        (profiledRawJointHybridPhysicalCompatibleLeftPayloadAt A strategy hwin
          state)
        member
  · obtain ⟨receiver, hpayload, hrow⟩ :=
      profiledRawJointHybridPhysicalCompatibleLeftPayloadAt_row A strategy hwin
        state move hmove
    exact ⟨receiver, by simpa
      [profiledRawJointHybridPhysicalCompatibleLeftOperationalForkAt,
        profiledRawJointHybridPhysicalCompatibleLeftForkAt,
        FiniteAcknowledgedDelayedCarrier.keyedDeferredMemberFork,
        FiniteDelayedFork.candidate] using hpayload.symm, by
          simpa [receiver] using rfl, hrow⟩

/-! ## Row-selected close and crossed refork -/

/-- A right close result exposes the selected target together with the newly
acknowledged left carrier. -/
noncomputable abbrev
    ProfiledRawJointHybridPhysicalCompatibleRightCloseResult
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  SuccessorTarget A strategy hwin initial ×
    FiniteAcknowledgedDelayedCarrier (Fin 5)
      (ProfiledRawJointHybridPhysicalCompatibleLeftDeferredControl A strategy
        hwin policy
        (ProfiledRawJointHybridPhysicalCompatibleLeftPayload A strategy hwin))

/-- Left-close result. -/
noncomputable abbrev
    ProfiledRawJointHybridPhysicalCompatibleLeftCloseResult
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  SuccessorTarget A strategy hwin initial ×
    FiniteAcknowledgedDelayedCarrier (Fin 5)
      (ProfiledRawJointHybridPhysicalCompatibleRightDeferredControl A strategy
        hwin policy
        (ProfiledRawJointHybridPhysicalCompatibleRightPayload A strategy hwin))

/-- Close a staged right receiver and refork the crossed left carrier.  The
only row read is the receiver's stored finite row. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleRightCloseRefork
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    {Control : Type c} {Delivered : Type d}
    (own : FiniteAcknowledgedDelayedCarrier (Fin 5) Control)
    (partner : FiniteAcknowledgedDelayedCarrier (Fin 5) Delivered)
    (receiver :
      ProfiledRawJointHybridPhysicalCompatibleRightReceiverState A strategy
        hwin (initial := initial)) :
    Option
      (ProfiledRawJointHybridPhysicalCompatibleRightCloseResult A strategy
        hwin policy) :=
  match receiver.2.2.2 with
  | none => none
  | some output =>
      let target := (output.target receiver.2.1).1
      some (target,
        FiniteAcknowledgedDelayedCarrier.refork own partner
          (profiledRawJointHybridPhysicalCompatibleLeftOperationalForkAt A
            strategy hwin policy
            (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A
              strategy hwin target)))

/-- Left close. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleLeftCloseRefork
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    {Control : Type c} {Delivered : Type d}
    (own : FiniteAcknowledgedDelayedCarrier (Fin 5) Control)
    (partner : FiniteAcknowledgedDelayedCarrier (Fin 5) Delivered)
    (receiver :
      ProfiledRawJointHybridPhysicalCompatibleLeftReceiverState A strategy hwin
        (initial := initial)) :
    Option
      (ProfiledRawJointHybridPhysicalCompatibleLeftCloseResult A strategy hwin
        policy) :=
  match receiver.2.2.2 with
  | none => none
  | some output =>
      let target := (output.target receiver.2.1).1
      some (target,
        FiniteAcknowledgedDelayedCarrier.refork own partner
          (profiledRawJointHybridPhysicalCompatibleRightOperationalForkAt A
            strategy hwin policy
            (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A
              strategy hwin target)))

@[simp] theorem
    profiledRawJointHybridPhysicalCompatibleRightCloseRefork_staged
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    {Control : Type c} {Delivered : Type d}
    (own : FiniteAcknowledgedDelayedCarrier (Fin 5) Control)
    (partner : FiniteAcknowledgedDelayedCarrier (Fin 5) Delivered)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (row : PairedEntryRow)
    (monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A strategy
        hwin (initial := initial) move false).State)
    (output : RightOutput A strategy hwin initial) :
    profiledRawJointHybridPhysicalCompatibleRightCloseRefork A strategy hwin
        policy own partner ⟨move, row, monitorState, some output⟩ =
      let target := (output.target row).1
      some (target,
        FiniteAcknowledgedDelayedCarrier.refork own partner
          (profiledRawJointHybridPhysicalCompatibleLeftOperationalForkAt A
            strategy hwin policy
            (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A
              strategy hwin target))) :=
  rfl

@[simp] theorem
    profiledRawJointHybridPhysicalCompatibleLeftCloseRefork_staged
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    {Control : Type c} {Delivered : Type d}
    (own : FiniteAcknowledgedDelayedCarrier (Fin 5) Control)
    (partner : FiniteAcknowledgedDelayedCarrier (Fin 5) Delivered)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (row : PairedEntryRow)
    (monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A strategy
        hwin (initial := initial) move false).State)
    (output : LeftOutput A strategy hwin initial) :
    profiledRawJointHybridPhysicalCompatibleLeftCloseRefork A strategy hwin
        policy own partner ⟨move, row, monitorState, some output⟩ =
      let target := (output.target row).1
      some (target,
        FiniteAcknowledgedDelayedCarrier.refork own partner
          (profiledRawJointHybridPhysicalCompatibleRightOperationalForkAt A
            strategy hwin policy
            (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A
              strategy hwin target))) :=
  rfl

/-- A close from a `.first` receiver selects a target tagged `.first`. -/
theorem profiledRawJointHybridPhysicalCompatibleRightCloseTarget_row_first
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (output : RightOutput A strategy hwin initial) :
    profiledRawJointHybridPhysicalCompatibleSuccessorTargetRow A strategy hwin
        (output.target .first).1 = .first :=
  (output.target .first).2

/-- Left mirror. -/
theorem profiledRawJointHybridPhysicalCompatibleLeftCloseTarget_row_first
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (output : LeftOutput A strategy hwin initial) :
    profiledRawJointHybridPhysicalCompatibleSuccessorTargetRow A strategy hwin
        (output.target .first).1 = .first :=
  (output.target .first).2

-/

end

end DetParityAutomaton

end DistributedSynthesis
