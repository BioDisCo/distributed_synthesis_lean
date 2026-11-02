/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndOperationalFamilyAutomaton
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndRootFamilyHandoff

/-!
# Executable receiver steps for end-to-end root families

The shared family overlay is the blind sender's local control.  A receiver
also needs an executable projection of the same table: for its proof-side
member, read the receiver component, advance the exact restarted monitor, and
stage an opposite-orientation recurrent macro only after the source-specific
physical-close and fixed-policy checks succeed.

This file supplies that primitive for all six restart sources.  The returned
restart root keeps the same source and replaces only its monitor state.  The
member index is an argument of the correctness-side projection; it is not
stored by either local sender control.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

open PairedStrategyMemory
open PairedStrategyMemory.PairedInitialProfiledRationalPackage

variable (package : PairedInitialProfiledRationalPackage A)

/-! ## Member labels of the shared tables -/

/-- Receiver label of one proof-side right-family member at the current shared
sender control.  The returned sender component is still the one common family
sender table. -/
noncomputable def endToEndRightFamilyMemberLabel
    (state : EndToEndRightFamilyOneControl A package) (member : Bool) :
    NarrowedBlockLabel In₂ In₁ (ProfiledRightReceiverOutput A) Out₁
      (((state.1.1 member).1.monitor A package).State) := by
  let monitors := endToEndRightFamilyRootMonitors A package state.1.1
  let family := state.1.2.toTransitionRationalTree
  let controller := finiteRootMemberController monitors family member
  exact controller.labelOf
    (state.2.memberControl monitors family member)

/-- Left-family mirror. -/
noncomputable def endToEndLeftFamilyMemberLabel
    (state : EndToEndLeftFamilyTwoControl A package) (member : Bool) :
    NarrowedBlockLabel In₁ In₂ (ProfiledLeftReceiverOutput A) Out₂
      (((state.1.1 member).1.monitor A package).State) := by
  let monitors := endToEndLeftFamilyRootMonitors A package state.1.1
  let family := state.1.2.toTransitionRationalTree
  let controller := finiteRootMemberController monitors family member
  exact controller.labelOf
    (state.2.memberControl monitors family member)

/-! ## Source-indexed executable receiver steps -/

/-- Unified result of a right-family receiver round. -/
abbrev EndToEndRightFamilyReceiverRoundResult :=
  ProfiledRightReceiverOutput A × EndToEndRightRestartRoot A package ×
    Option (EndToEndRecurrentLeftMacro A package)

/-- Unified left-family result. -/
abbrev EndToEndLeftFamilyReceiverRoundResult :=
  ProfiledLeftReceiverOutput A × EndToEndLeftRestartRoot A package ×
    Option (EndToEndRecurrentRightMacro A package)

/-- Execute one right-family receiver round for an exact monitor source.

The exceptional source checks its guarded first-block policy.  The two
recurrent sources check the ordinary fixed policy below their retained child.
In every branch the physical-close equality and policy membership are the
proofs used to construct the typed opposite macro. -/
noncomputable def stepEndToEndRightFamilyReceiverSource
    (source : EndToEndRightMonitorSource A package)
    (label : NarrowedBlockLabel In₂ In₁
      (ProfiledRightReceiverOutput A) Out₁ (source.monitor A package).State)
    (row : PairedEntryRow) (monitorState : (source.monitor A package).State)
    (move : In₂ × In₁) :
    EndToEndRightFamilyReceiverRoundResult A package := by
  classical
  let output := label.2 monitorState move
  let physical := profiledRightPhysicalLetter A (move, output, label.1 move.2)
  let nextMonitor := (source.monitor A package).step monitorState
    (move, output, label.1 move.2)
  cases source with
  | first key =>
      let activation := endToEndInitialLeftBoundaryActivation A package key
      if hsafe : erasePairedProfiledState A (output.target row) =
            pairedRightCloseTarget A monitorState.2.1 row physical ∧
          ProfiledGuardedRightPolicyAllows A key.1.2.2.2 activation.profile
            activation.policy (output.target row) then
        let child : EndToEndGuardedRightChild A key.1.2.2.2
            activation.profile activation.policy :=
          ⟨output.target row, hsafe.2⟩
        exact (output, ⟨.first key, nextMonitor⟩,
          some (.inl ⟨key,
            child.recurrentLeftMacroOfClose A monitorState.2.1 row physical
              hsafe.1⟩))
      else
        exact (output, ⟨.first key, nextMonitor⟩, none)
  | rightOrigin recurrent =>
      if hsafe : erasePairedProfiledState A (output.target row) =
            pairedRightCloseTarget A monitorState.2.1 row physical ∧
          PairedProfiledRationalPolicy.Allowed A (recurrent.2.1.policy A)
            (.inr (.inl recurrent.2.2.1)) (output.target row) then
        exact (output, ⟨.rightOrigin recurrent, nextMonitor⟩,
          some (.inl ⟨recurrent.1,
            endToEndGuardedRightRecurrentLeftOfRightCertificate A recurrent.2
              (output.target row) monitorState.2.1 row physical hsafe.1
              hsafe.2⟩))
      else
        exact (output, ⟨.rightOrigin recurrent, nextMonitor⟩, none)
  | leftOrigin recurrent =>
      if hsafe : erasePairedProfiledState A (output.target row) =
            pairedRightCloseTarget A monitorState.2.1 row physical ∧
          PairedProfiledRationalPolicy.Allowed A (recurrent.2.1.policy A)
            (.inr (.inl recurrent.2.2.1)) (output.target row) then
        exact (output, ⟨.leftOrigin recurrent, nextMonitor⟩,
          some (.inr ⟨recurrent.1,
            endToEndGuardedLeftRecurrentLeftOfRightCertificate A recurrent.2
              (output.target row) monitorState.2.1 row physical hsafe.1
              hsafe.2⟩))
      else
        exact (output, ⟨.leftOrigin recurrent, nextMonitor⟩, none)

/-- Execute one left-family receiver round, covering the exceptional first
source and both recurrent origins. -/
noncomputable def stepEndToEndLeftFamilyReceiverSource
    (source : EndToEndLeftMonitorSource A package)
    (label : NarrowedBlockLabel In₁ In₂
      (ProfiledLeftReceiverOutput A) Out₂ (source.monitor A package).State)
    (row : PairedEntryRow) (monitorState : (source.monitor A package).State)
    (move : In₁ × In₂) :
    EndToEndLeftFamilyReceiverRoundResult A package := by
  classical
  let output := label.2 monitorState move
  let physical := profiledLeftPhysicalLetter A (move, output, label.1 move.2)
  let nextMonitor := (source.monitor A package).step monitorState
    (move, output, label.1 move.2)
  cases source with
  | first key =>
      let activation := endToEndInitialRightBoundaryActivation A package key
      if hsafe : erasePairedProfiledState A (output.target row) =
            pairedLeftCloseTarget A monitorState.2.1 row physical ∧
          ProfiledGuardedLeftPolicyAllows A key.1.2.2.2 activation.profile
            activation.policy (output.target row) then
        let child : EndToEndGuardedLeftChild A key.1.2.2.2
            activation.profile activation.policy :=
          ⟨output.target row, hsafe.2⟩
        exact (output, ⟨.first key, nextMonitor⟩,
          some (.inr ⟨key,
            child.recurrentRightMacroOfClose A monitorState.2.1 row physical
              hsafe.1⟩))
      else
        exact (output, ⟨.first key, nextMonitor⟩, none)
  | rightOrigin recurrent =>
      if hsafe : erasePairedProfiledState A (output.target row) =
            pairedLeftCloseTarget A monitorState.2.1 row physical ∧
          PairedProfiledRationalPolicy.Allowed A (recurrent.2.1.policy A)
            (.inr (.inr recurrent.2.2.1)) (output.target row) then
        exact (output, ⟨.rightOrigin recurrent, nextMonitor⟩,
          some (.inl ⟨recurrent.1,
            endToEndGuardedRightRecurrentRightOfLeftCertificate A recurrent.2
              (output.target row) monitorState.2.1 row physical hsafe.1
              hsafe.2⟩))
      else
        exact (output, ⟨.rightOrigin recurrent, nextMonitor⟩, none)
  | leftOrigin recurrent =>
      if hsafe : erasePairedProfiledState A (output.target row) =
            pairedLeftCloseTarget A monitorState.2.1 row physical ∧
          PairedProfiledRationalPolicy.Allowed A (recurrent.2.1.policy A)
            (.inr (.inr recurrent.2.2.1)) (output.target row) then
        exact (output, ⟨.leftOrigin recurrent, nextMonitor⟩,
          some (.inr ⟨recurrent.1,
            endToEndGuardedLeftRecurrentRightOfLeftCertificate A recurrent.2
              (output.target row) monitorState.2.1 row physical hsafe.1
              hsafe.2⟩))
      else
        exact (output, ⟨.leftOrigin recurrent, nextMonitor⟩, none)

/-! ## Family-table entry points -/

/-- Execute the receiver projection of one member of the actual shared right
family overlay. -/
noncomputable def stepEndToEndRightFamilyReceiver
    (state : EndToEndRightFamilyOneControl A package) (member : Bool)
    (row : PairedEntryRow)
    (monitorState : ((state.1.1 member).1.monitor A package).State)
    (move : In₂ × In₁) :
    EndToEndRightFamilyReceiverRoundResult A package :=
  stepEndToEndRightFamilyReceiverSource A package (state.1.1 member).1
    (endToEndRightFamilyMemberLabel A package state member) row monitorState move

/-- Left-family mirror. -/
noncomputable def stepEndToEndLeftFamilyReceiver
    (state : EndToEndLeftFamilyTwoControl A package) (member : Bool)
    (row : PairedEntryRow)
    (monitorState : ((state.1.1 member).1.monitor A package).State)
    (move : In₁ × In₂) :
    EndToEndLeftFamilyReceiverRoundResult A package :=
  stepEndToEndLeftFamilyReceiverSource A package (state.1.1 member).1
    (endToEndLeftFamilyMemberLabel A package state member) row monitorState move

/-- Start the right receiver projection at the monitor state stored in the
member's restart root. -/
noncomputable def initialStepEndToEndRightFamilyReceiver
    (state : EndToEndRightFamilyOneControl A package) (member : Bool)
    (row : PairedEntryRow) (move : In₂ × In₁) :
    EndToEndRightFamilyReceiverRoundResult A package :=
  stepEndToEndRightFamilyReceiver A package state member row
    (state.1.1 member).2 move

/-- Left-family mirror. -/
noncomputable def initialStepEndToEndLeftFamilyReceiver
    (state : EndToEndLeftFamilyTwoControl A package) (member : Bool)
    (row : PairedEntryRow) (move : In₁ × In₂) :
    EndToEndLeftFamilyReceiverRoundResult A package :=
  stepEndToEndLeftFamilyReceiver A package state member row
    (state.1.1 member).2 move

/-! ## Executable bookkeeping laws -/

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

/-- A right receiver step preserves its exact monitor source. -/
theorem stepEndToEndRightFamilyReceiverSource_source
    (source : EndToEndRightMonitorSource A package)
    (label : NarrowedBlockLabel In₂ In₁
      (ProfiledRightReceiverOutput A) Out₁ (source.monitor A package).State)
    (row : PairedEntryRow) (monitorState : (source.monitor A package).State)
    (move : In₂ × In₁) :
    (stepEndToEndRightFamilyReceiverSource A package source label row
      monitorState move).2.1.1 = source := by
  classical
  cases source <;>
    simp only [stepEndToEndRightFamilyReceiverSource] <;>
    split <;> rfl

/-- Left-oriented source preservation. -/
theorem stepEndToEndLeftFamilyReceiverSource_source
    (source : EndToEndLeftMonitorSource A package)
    (label : NarrowedBlockLabel In₁ In₂
      (ProfiledLeftReceiverOutput A) Out₂ (source.monitor A package).State)
    (row : PairedEntryRow) (monitorState : (source.monitor A package).State)
    (move : In₁ × In₂) :
    (stepEndToEndLeftFamilyReceiverSource A package source label row
      monitorState move).2.1.1 = source := by
  classical
  cases source <;>
    simp only [stepEndToEndLeftFamilyReceiverSource] <;>
    split <;> rfl

/-- The output of a right source step is exactly the receiver component of its
member label. -/
theorem stepEndToEndRightFamilyReceiverSource_output
    (source : EndToEndRightMonitorSource A package)
    (label : NarrowedBlockLabel In₂ In₁
      (ProfiledRightReceiverOutput A) Out₁ (source.monitor A package).State)
    (row : PairedEntryRow) (monitorState : (source.monitor A package).State)
    (move : In₂ × In₁) :
    (stepEndToEndRightFamilyReceiverSource A package source label row
      monitorState move).1 = label.2 monitorState move := by
  classical
  cases source <;>
    simp only [stepEndToEndRightFamilyReceiverSource] <;>
    split <;> rfl

/-- Left source-step output equation. -/
theorem stepEndToEndLeftFamilyReceiverSource_output
    (source : EndToEndLeftMonitorSource A package)
    (label : NarrowedBlockLabel In₁ In₂
      (ProfiledLeftReceiverOutput A) Out₂ (source.monitor A package).State)
    (row : PairedEntryRow) (monitorState : (source.monitor A package).State)
    (move : In₁ × In₂) :
    (stepEndToEndLeftFamilyReceiverSource A package source label row
      monitorState move).1 = label.2 monitorState move := by
  classical
  cases source <;>
    simp only [stepEndToEndLeftFamilyReceiverSource] <;>
    split <;> rfl

/-- A right source step preserves the source and advances precisely its monitor
on the physical round emitted by the member label.  Stating this for the whole
dependent restart root avoids transporting a state across a separately proved
source equality. -/
theorem stepEndToEndRightFamilyReceiverSource_restartRoot
    (source : EndToEndRightMonitorSource A package)
    (label : NarrowedBlockLabel In₂ In₁
      (ProfiledRightReceiverOutput A) Out₁ (source.monitor A package).State)
    (row : PairedEntryRow) (monitorState : (source.monitor A package).State)
    (move : In₂ × In₁) :
    (stepEndToEndRightFamilyReceiverSource A package source label row
      monitorState move).2.1 =
      ⟨source, (source.monitor A package).step monitorState
        (move, label.2 monitorState move, label.1 move.2)⟩ := by
  classical
  cases source <;>
    simp only [stepEndToEndRightFamilyReceiverSource] <;>
    split <;> rfl

/-- Left source-step restart-root equation. -/
theorem stepEndToEndLeftFamilyReceiverSource_restartRoot
    (source : EndToEndLeftMonitorSource A package)
    (label : NarrowedBlockLabel In₁ In₂
      (ProfiledLeftReceiverOutput A) Out₂ (source.monitor A package).State)
    (row : PairedEntryRow) (monitorState : (source.monitor A package).State)
    (move : In₁ × In₂) :
    (stepEndToEndLeftFamilyReceiverSource A package source label row
      monitorState move).2.1 =
      ⟨source, (source.monitor A package).step monitorState
        (move, label.2 monitorState move, label.1 move.2)⟩ := by
  classical
  cases source <;>
    simp only [stepEndToEndLeftFamilyReceiverSource] <;>
    split <;> rfl

/-- The right member output is exactly the receiver component of the shared
family label. -/
theorem stepEndToEndRightFamilyReceiver_output
    (state : EndToEndRightFamilyOneControl A package) (member : Bool)
    (row : PairedEntryRow)
    (monitorState : ((state.1.1 member).1.monitor A package).State)
    (move : In₂ × In₁) :
    (stepEndToEndRightFamilyReceiver A package state member row monitorState
      move).1 =
      (endToEndRightFamilyMemberLabel A package state member).2 monitorState
        move := by
  simpa only [stepEndToEndRightFamilyReceiver] using
    (stepEndToEndRightFamilyReceiverSource_output A package
      (state.1.1 member).1
      (endToEndRightFamilyMemberLabel A package state member) row monitorState move)

/-- Left-family output equation. -/
theorem stepEndToEndLeftFamilyReceiver_output
    (state : EndToEndLeftFamilyTwoControl A package) (member : Bool)
    (row : PairedEntryRow)
    (monitorState : ((state.1.1 member).1.monitor A package).State)
    (move : In₁ × In₂) :
    (stepEndToEndLeftFamilyReceiver A package state member row monitorState
      move).1 =
      (endToEndLeftFamilyMemberLabel A package state member).2 monitorState
        move := by
  simpa only [stepEndToEndLeftFamilyReceiver] using
    (stepEndToEndLeftFamilyReceiverSource_output A package
      (state.1.1 member).1
      (endToEndLeftFamilyMemberLabel A package state member) row monitorState move)

end

end

end DetParityAutomaton

end DistributedSynthesis
