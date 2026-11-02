/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndRestartRoot
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRootFamilyLocalOverlay

/-!
# Simultaneous root-family overlays for the one-policy end-to-end carrier

The earlier profiled root-family move may select a new feasible policy at a
recurrent root.  It is therefore too coarse for the final end-to-end carrier,
whose parity proof follows one fixed child policy through every reversal.

This file instantiates the generic simultaneous family table with the exact
restart roots of `ThmPairedProfiledEndToEndRestartRoot`.  A move contains two
proof-side roots and one shared sender table.  Its local overlay contains no
root index, orientation bit, anchor, or strict-leader signal.  Consequently
both hidden roots have definitionally the same blind output and successor
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

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

open PairedStrategyMemory
open PairedStrategyMemory.PairedInitialProfiledRationalPackage

variable (package : PairedInitialProfiledRationalPackage A)

/-! ## Fixed-policy family moves -/

/-- The two right restart monitors selected by a proof-side family map. -/
noncomputable abbrev endToEndRightFamilyRootMonitors
    (source : Bool → EndToEndRightRestartRoot A package) :=
  fun index => endToEndRightRestartRootMonitor A package (source index)

/-- Left-oriented mirror. -/
noncomputable abbrev endToEndLeftFamilyRootMonitors
    (source : Bool → EndToEndLeftRestartRoot A package) :=
  fun index => endToEndLeftRestartRootMonitor A package (source index)

/-- Literal simultaneous table for two right restart roots. -/
noncomputable abbrev EndToEndRightFamilyRootTable
    (source : Bool → EndToEndRightRestartRoot A package) :=
  FiniteRootFamilyTable (endToEndRightFamilyRootMonitors A package source)

/-- Literal simultaneous table for two left restart roots. -/
noncomputable abbrev EndToEndLeftFamilyRootTable
    (source : Bool → EndToEndLeftRestartRoot A package) :=
  FiniteRootFamilyTable (endToEndLeftFamilyRootMonitors A package source)

/-- Two right roots together with their one shared finite table. -/
abbrev EndToEndRightFamilyPairMove :=
  Σ source : Bool → EndToEndRightRestartRoot A package,
    EndToEndRightFamilyRootTable A package source

/-- Left-oriented mirror. -/
abbrev EndToEndLeftFamilyPairMove :=
  Σ source : Bool → EndToEndLeftRestartRoot A package,
    EndToEndLeftFamilyRootTable A package source

noncomputable instance : Fintype (EndToEndRightFamilyPairMove A package) := by
  classical
  infer_instance

noncomputable instance : Fintype (EndToEndLeftFamilyPairMove A package) := by
  classical
  infer_instance

/-! ## Shared local overlays -/

/-- A right pair move together with the one process-one local state shared by
both of its hidden projections. -/
abbrev EndToEndRightFamilyPairOverlay :=
  Σ move : EndToEndRightFamilyPairMove A package,
    FiniteRootFamilyLocalOverlay
      (endToEndRightFamilyRootMonitors A package move.1)
      move.2.toTransitionRationalTree

/-- A left pair move together with the one process-two shared local state. -/
abbrev EndToEndLeftFamilyPairOverlay :=
  Σ move : EndToEndLeftFamilyPairMove A package,
    FiniteRootFamilyLocalOverlay
      (endToEndLeftFamilyRootMonitors A package move.1)
      move.2.toTransitionRationalTree

noncomputable instance : Fintype
    (EndToEndRightFamilyPairOverlay A package) := by
  classical
  infer_instance

noncomputable instance : Fintype
    (EndToEndLeftFamilyPairOverlay A package) := by
  classical
  infer_instance

/-- Install a right family at its one shared initial sender state. -/
def EndToEndRightFamilyPairOverlay.initial
    (move : EndToEndRightFamilyPairMove A package) :
    EndToEndRightFamilyPairOverlay A package :=
  ⟨move, FiniteRootFamilyLocalOverlay.initial
    (endToEndRightFamilyRootMonitors A package move.1)
    move.2.toTransitionRationalTree⟩

/-- Left-oriented mirror. -/
def EndToEndLeftFamilyPairOverlay.initial
    (move : EndToEndLeftFamilyPairMove A package) :
    EndToEndLeftFamilyPairOverlay A package :=
  ⟨move, FiniteRootFamilyLocalOverlay.initial
    (endToEndLeftFamilyRootMonitors A package move.1)
    move.2.toTransitionRationalTree⟩

/-- Advance the shared process-one state. -/
def EndToEndRightFamilyPairOverlay.step
    (state : EndToEndRightFamilyPairOverlay A package) (input : In₁) :
    EndToEndRightFamilyPairOverlay A package :=
  ⟨state.1, state.2.step
    (endToEndRightFamilyRootMonitors A package state.1.1)
    state.1.2.toTransitionRationalTree input⟩

/-- Advance the shared process-two state. -/
def EndToEndLeftFamilyPairOverlay.step
    (state : EndToEndLeftFamilyPairOverlay A package) (input : In₂) :
    EndToEndLeftFamilyPairOverlay A package :=
  ⟨state.1, state.2.step
    (endToEndLeftFamilyRootMonitors A package state.1.1)
    state.1.2.toTransitionRationalTree input⟩

/-! ## Member-step interface -/

/-- Common finite control type of the two right projections. -/
abbrev EndToEndRightFamilyPairOverlay.MemberControl
    (state : EndToEndRightFamilyPairOverlay A package) :=
  (finiteRootMemberController
    (endToEndRightFamilyRootMonitors A package state.1.1)
    state.1.2.toTransitionRationalTree false).Control

/-- Common finite control type of the two left projections. -/
abbrev EndToEndLeftFamilyPairOverlay.MemberControl
    (state : EndToEndLeftFamilyPairOverlay A package) :=
  (finiteRootMemberController
    (endToEndLeftFamilyRootMonitors A package state.1.1)
    state.1.2.toTransitionRationalTree false).Control

/-- Output and next process-one control of one hidden right member. -/
def EndToEndRightFamilyPairOverlay.memberStep
    (state : EndToEndRightFamilyPairOverlay A package) (member : Bool)
    (input : In₁) : Out₁ × state.MemberControl A package :=
  let monitors := endToEndRightFamilyRootMonitors A package state.1.1
  let family := state.1.2.toTransitionRationalTree
  let shared := state.2
  (((finiteRootMemberController monitors family member).labelOf
      (shared.memberControl monitors family member)).1 input,
    (finiteRootMemberController monitors family member).step
      (shared.memberControl monitors family member) input)

/-- Process-two mirror. -/
def EndToEndLeftFamilyPairOverlay.memberStep
    (state : EndToEndLeftFamilyPairOverlay A package) (member : Bool)
    (input : In₂) : Out₂ × state.MemberControl A package :=
  let monitors := endToEndLeftFamilyRootMonitors A package state.1.1
  let family := state.1.2.toTransitionRationalTree
  let shared := state.2
  (((finiteRootMemberController monitors family member).labelOf
      (shared.memberControl monitors family member)).1 input,
    (finiteRootMemberController monitors family member).step
      (shared.memberControl monitors family member) input)

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- The right member step is independent of the hidden proof anchor. -/
theorem EndToEndRightFamilyPairOverlay.memberStep_eq
    (state : EndToEndRightFamilyPairOverlay A package) (left right : Bool)
    (input : In₁) :
    state.memberStep A package left input =
      state.memberStep A package right input := by
  exact FiniteRootFamilyLocalOverlay.localStep_eq
    (endToEndRightFamilyRootMonitors A package state.1.1)
    state.1.2.toTransitionRationalTree state.2 left right input

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- The left member step is independent of the hidden proof anchor. -/
theorem EndToEndLeftFamilyPairOverlay.memberStep_eq
    (state : EndToEndLeftFamilyPairOverlay A package) (left right : Bool)
    (input : In₂) :
    state.memberStep A package left input =
      state.memberStep A package right input := by
  exact FiniteRootFamilyLocalOverlay.localStep_eq
    (endToEndLeftFamilyRootMonitors A package state.1.1)
    state.1.2.toTransitionRationalTree state.2 left right input

end

end DetParityAutomaton

end DistributedSynthesis
