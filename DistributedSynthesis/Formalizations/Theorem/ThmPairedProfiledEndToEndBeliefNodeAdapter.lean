/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndJointSafetyGame

/-!
# A downstream source-free belief node for the joint family construction

This file isolates finite data of the existing end-to-end joint-family
controller.  It is a **downstream conditional adapter**, not the missing
pre-rationalization construction: all types below are parameterized by
`PairedInitialProfiledRationalPackage`, which already contains rational block
policies.

* A belief code is the pair of ordinary local family summaries, their two
  locally observed receipt bits, and the current input pair.
* A move is one simultaneous choice of the right and left family tables.
* A direction contains the graph and the next input pair, and is read only
  after the move has been chosen.

None of these types contains a selected family member, a current orientation,
or a strict-leader bit.  The transition is the already total joint-family
transition.  Its local T1 law is structural: both hidden projections of each
family table have literally the same blind output and successor control.  In
particular this law does not assume semantic representability, pointed
compatibility, or a right congruence.

This brick therefore does not claim raw-winner existence or the remaining
semantic thread theorem.  A genuinely pre-rationalization adapter must first
construct the analogous bidirectional open-family node directly from the raw
winning strategy.  Its thread theorem must show that the proof-side semantic
history at one node is carried to a semantic history at every real successor,
and that the resulting coherent infinite thread has the required parity.
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

/-! ## Finite source-free node data -/

/-- The finite public code at a joint family decision.  The current graph is
absent; it is revealed only by the following direction. -/
abbrev EndToEndFamilyBeliefCode :=
  EndToEndFamilyReceiveObservation A package

/-- One shared label installs both orientation tables at once. -/
abbrev EndToEndFamilyBeliefMove :=
  EndToEndFamilyJointMove A package

/-- Nature's resolution after the shared label has been chosen. -/
abbrev EndToEndFamilyBeliefDirection :=
  EndToEndFamilySafetyBranch (In₁ := In₁) (In₂ := In₂)

noncomputable instance : Fintype (EndToEndFamilyBeliefCode A package) := by
  classical
  infer_instance

noncomputable instance : Fintype (EndToEndFamilyBeliefMove A package) := by
  classical
  infer_instance

noncomputable instance : Fintype
    (EndToEndFamilyBeliefDirection (In₁ := In₁) (In₂ := In₂)) := by
  classical
  infer_instance

/-- Purely structural node validity.  It says only that both tables are
indexed by the two source families computed from the finite code.  Parity of
their hidden threads is kept in the separate `ThreadValid` predicate below. -/
def EndToEndFamilyBeliefValid
    (code : EndToEndFamilyBeliefCode A package)
    (move : EndToEndFamilyBeliefMove A package) : Prop :=
  move.1.1 = (code.post A package).rightSource A package ∧
    move.2.1 = (code.post A package).leftSource A package

/-- The universal parity part of a joint label.  This is the exact model
content to be supplied to the generic coherent-thread field; it is not used
to prove local T1. -/
def EndToEndFamilyBeliefThreadValid
    (move : EndToEndFamilyBeliefMove A package) : Prop :=
  EndToEndRightFamilyRootTableWins A package move.1.1 move.1.2 ∧
    EndToEndLeftFamilyRootTableWins A package move.2.1 move.2.2

/-- The old joint-game legality is exactly structural validity together with
the two universal family-thread certificates. -/
theorem endToEndFamilyJointMove_legalAt_iff_beliefValid_threadValid
    (code : EndToEndFamilyBeliefCode A package)
    (move : EndToEndFamilyBeliefMove A package) :
    EndToEndFamilyJointMove.LegalAt A package code move ↔
      EndToEndFamilyBeliefValid A package code move ∧
        EndToEndFamilyBeliefThreadValid A package move := by
  simp only [EndToEndFamilyJointMove.LegalAt,
    EndToEndFamilyBeliefValid, EndToEndFamilyBeliefThreadValid, and_assoc]

/-- Total source-free successor.  The direction is consumed after the common
move; no hidden member is an argument. -/
noncomputable def endToEndFamilyBeliefNext
    (code : EndToEndFamilyBeliefCode A package)
    (move : EndToEndFamilyBeliefMove A package)
    (direction : EndToEndFamilyBeliefDirection
      (In₁ := In₁) (In₂ := In₂)) :
    EndToEndFamilyBeliefCode A package :=
  endToEndFamilyJointSafetyNext A package code move direction

/-! ## Structural T1 -/

/-- Local T1 for one source-free joint label.  Both possible right members
have one process-one step, and both possible left members have one process-two
step.  The statement is independent of which member is the real one. -/
def EndToEndFamilyBeliefMove.StructuralT1
    (move : EndToEndFamilyBeliefMove A package) : Prop :=
  (∀ (left right : Bool) (input : In₁),
      (EndToEndRightFamilyPairOverlay.initial A package move.1).memberStep
          A package left input =
        (EndToEndRightFamilyPairOverlay.initial A package move.1).memberStep
          A package right input) ∧
    (∀ (left right : Bool) (input : In₂),
      (EndToEndLeftFamilyPairOverlay.initial A package move.2).memberStep
          A package left input =
        (EndToEndLeftFamilyPairOverlay.initial A package move.2).memberStep
          A package right input)

/-- Every finite joint label satisfies local T1 by construction.  No winning
or semantic premise is needed. -/
theorem endToEndFamilyBeliefMove_structuralT1
    (move : EndToEndFamilyBeliefMove A package) :
    move.StructuralT1 A package := by
  constructor
  · intro left right input
    exact EndToEndRightFamilyPairOverlay.memberStep_eq A package
      (EndToEndRightFamilyPairOverlay.initial A package move.1)
      left right input
  · intro left right input
    exact EndToEndLeftFamilyPairOverlay.memberStep_eq A package
      (EndToEndLeftFamilyPairOverlay.initial A package move.2)
      left right input

/-- The exact T1 package consumed at a finite belief node: syntactic validity
plus member-independent local behavior. -/
def EndToEndFamilyBeliefT1
    (code : EndToEndFamilyBeliefCode A package)
    (move : EndToEndFamilyBeliefMove A package) : Prop :=
  EndToEndFamilyBeliefValid A package code move ∧
    move.StructuralT1 A package

/-- Hence the model's T1 field reduces definitionally to `Valid`; the
cross-anchor part is already unconditional. -/
theorem endToEndFamilyBeliefT1_of_valid
    (code : EndToEndFamilyBeliefCode A package)
    (move : EndToEndFamilyBeliefMove A package)
    (hvalid : EndToEndFamilyBeliefValid A package code move) :
    EndToEndFamilyBeliefT1 A package code move :=
  ⟨hvalid, endToEndFamilyBeliefMove_structuralT1 A package move⟩

/-! ## Exact graph-blind ordering equations -/

/-- The graph is genuinely a successor direction: fixing the code and move
fixes the computation performed before the graph case split. -/
theorem endToEndFamilyBeliefNext_eq_jointSafetyNext
    (code : EndToEndFamilyBeliefCode A package)
    (move : EndToEndFamilyBeliefMove A package)
    (direction : EndToEndFamilyBeliefDirection
      (In₁ := In₁) (In₂ := In₂)) :
    endToEndFamilyBeliefNext A package code move direction =
      endToEndFamilyJointSafetyNext A package code move direction :=
  rfl

/-- On a simultaneous receive, the two local summaries install projections
of the very same joint move. -/
theorem endToEndFamilyBeliefNext_both_installs_common_move
    (code : EndToEndFamilyBeliefCode A package)
    (move : EndToEndFamilyBeliefMove A package)
    (nextInputOne : In₁) (nextInputTwo : In₂) :
    let next := endToEndFamilyBeliefNext A package code move
      (.both, nextInputOne, nextInputTwo)
    next.one.1.1.rightSender.1 = move.1 ∧
      next.two.1.1.leftSender.1 = move.2 := by
  dsimp only [endToEndFamilyBeliefNext,
    endToEndFamilyJointSafetyNext,
    endToEndFamilyJointSafetySummaryNext]
  exact ⟨rfl, rfl⟩

end

end DetParityAutomaton

end DistributedSynthesis
