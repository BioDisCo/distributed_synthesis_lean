/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedEntryTransitionFactorMirror
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenOverlayEpochSlice

/-!
# Fail-fast audit of the shifted `.both` restart

The FullRestart controller emits the strict block's entry record with row
`.first` and all later records with row `.both`.  A tempting acceptance splice
is therefore to discard that first record and start the old fixed-`.both`
table at the shifted boundary.

This file checks the DPA-state equation required by that splice before any
further controller plumbing is built.  The same-occurrence child construction
does not supply it: the child's `.first` coordinate is the actual strict
successor, whereas its `.both` coordinate is the counterfactual simultaneous
successor.  The generic equivalences below expose this distinction
definitionally.  The final tiny DPA separates strict and simultaneous records,
giving a kernel-checked counterexample in both orientations.

This does not refute FullRestart.  It rules out only the splice which changes
from the actual `.first` coordinate to the *same child's* `.both` coordinate.
A successful acceptance proof must retain the actual `.first` DPA state, or
exhibit a separately represented table occurrence whose advertised entry
state is literally that state.
-/

namespace DistributedSynthesis

namespace DetParityAutomaton

universe u v x y s

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

/-! ## The exact algebra demanded by a shifted-row splice -/

/-- For a same-occurrence right-to-left child, identifying the actual
`.first` entry with the shifted table's `.both` entry is exactly the assertion
that the strict and simultaneous successor records have the same DPA image. -/
theorem pairedRightFreshChildCodeLeft_first_eq_both_iff
    (code : A.State × A.State)
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    let oldState := (pairedRightSuccessorCode A code lambda past).1
    let child := pairedRightFreshChildCodeLeft A code lambda past move
    pairedCodeStateForRow A .first child =
        pairedCodeStateForRow A .both child ↔
      A.step oldState
          (rightRoundRecord move
            (lambda.blind (senderWord past) move.2)
            (lambda.informedLeft past move)) =
        A.step oldState
          (bothRoundRecord (move.2, move.1)
            (lambda.bothOneLeft past move)
            (lambda.informedLeft past move)) := by
  rfl

/-- Left-to-right mirror of the shifted-row equation. -/
theorem pairedLeftFreshChildCodeRight_first_eq_both_iff
    (code : A.State × A.State)
    (lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    let oldState := (pairedLeftSuccessorCode A code lambda past).1
    let child := pairedLeftFreshChildCodeRight A code lambda past move
    pairedCodeStateForRow A .first child =
        pairedCodeStateForRow A .both child ↔
      A.step oldState
          (leftRoundRecord move
            (lambda.informedRight past move)
            (lambda.blind (senderWord past) move.2)) =
        A.step oldState
          (bothRoundRecord move
            (lambda.informedRight past move)
            (lambda.bothTwoRight past move)) := by
  rfl

/-! ## A concrete separating DPA -/

/-- The smallest objective automaton needed for the audit.  It remembers only
whether the last record was simultaneous. -/
abbrev fullRestartShiftedBothStateTestDPA :
    DetParityAutomaton (RoundRecord Unit Unit Graph Unit Unit) where
  State := Bool
  stateFinite := inferInstance
  initial := false
  step _ record :=
    match record.graph with
    | .both => true
    | .left | .right => false
  priority _ := 0

/-- Trivial output behavior; all of the separation comes from the literal
strict-versus-simultaneous graph coordinate of the same occurrence. -/
def fullRestartShiftedBothStateTestRightLambda :
    ProcOnePairedRightLambda
      (In₁ := Unit) (In₂ := Unit) (Out₁ := Unit) (Out₂ := Unit) where
  blind := fun _ _ ↦ ()
  informedLeft := fun _ _ ↦ ()
  informedBoth := fun _ _ ↦ ()
  bothOneLeft := fun _ _ ↦ ()
  bothOneBoth := fun _ _ ↦ ()

/-- Mirror trivial lambda. -/
def fullRestartShiftedBothStateTestLeftLambda :
    ProcTwoPairedLeftLambda
      (In₁ := Unit) (In₂ := Unit) (Out₁ := Unit) (Out₂ := Unit) where
  blind := fun _ _ ↦ ()
  informedRight := fun _ _ ↦ ()
  informedBoth := fun _ _ ↦ ()
  bothTwoRight := fun _ _ ↦ ()
  bothTwoBoth := fun _ _ ↦ ()

/-- A literal same-occurrence right child has actual state `false` and
counterfactual `.both` state `true`. -/
theorem fullRestartShiftedBothStateTest_right_child_eq :
    pairedRightFreshChildCodeLeft fullRestartShiftedBothStateTestDPA
        (false, false) fullRestartShiftedBothStateTestRightLambda [] ((), ()) =
      (false, true) := by
  rfl

/-- Hence the shifted `.both` entry-state equation is false even for the
literal same-occurrence child constructor. -/
theorem fullRestartShiftedBothStateTest_right_first_ne_both :
    let child :=
      pairedRightFreshChildCodeLeft fullRestartShiftedBothStateTestDPA
        (false, false) fullRestartShiftedBothStateTestRightLambda [] ((), ())
    pairedCodeStateForRow fullRestartShiftedBothStateTestDPA .first child ≠
      pairedCodeStateForRow fullRestartShiftedBothStateTestDPA .both child := by
  dsimp only
  rw [fullRestartShiftedBothStateTest_right_child_eq]
  exact Bool.false_ne_true

/-- The mirror child has the same separation. -/
theorem fullRestartShiftedBothStateTest_left_child_eq :
    pairedLeftFreshChildCodeRight fullRestartShiftedBothStateTestDPA
        (false, false) fullRestartShiftedBothStateTestLeftLambda [] ((), ()) =
      (false, true) := by
  rfl

/-- Mirror refutation of the shifted `.both` entry-state equation. -/
theorem fullRestartShiftedBothStateTest_left_first_ne_both :
    let child :=
      pairedLeftFreshChildCodeRight fullRestartShiftedBothStateTestDPA
        (false, false) fullRestartShiftedBothStateTestLeftLambda [] ((), ())
    pairedCodeStateForRow fullRestartShiftedBothStateTestDPA .first child ≠
      pairedCodeStateForRow fullRestartShiftedBothStateTestDPA .both child := by
  dsimp only
  rw [fullRestartShiftedBothStateTest_left_child_eq]
  exact Bool.false_ne_true

/-! ## A later simultaneous round is not the stored `.both` coordinate -/

/-- This audit automaton distinguishes the time of the simultaneous record.
A strict record sets the state to `true`, whereas a simultaneous record keeps
the preceding state.  Thus the counterfactual simultaneous successor stored
with a strict occurrence need not equal the successor of a later simultaneous
round. -/
abbrev fullRestartDelayedBothStateTestDPA :
    DetParityAutomaton (RoundRecord Unit Unit Graph Unit Unit) where
  State := Bool
  stateFinite := inferInstance
  initial := false
  step state record :=
    match record.graph with
    | .both => state
    | .left | .right => true
  priority _ := 0

/-- After a strict-right occurrence, consuming a later simultaneous record
from the actual `.first` successor does not in general reach the same
occurrence's stored `.both` coordinate. -/
theorem fullRestartDelayedBothStateTest_right_postClose_ne_storedBoth :
    let child :=
      pairedRightFreshChildCodeLeft fullRestartDelayedBothStateTestDPA
        (false, false) fullRestartShiftedBothStateTestRightLambda [] ((), ())
    fullRestartDelayedBothStateTestDPA.step
        (pairedCodeStateForRow fullRestartDelayedBothStateTestDPA .first child)
        (bothRoundRecord ((), ()) () ()) ≠
      pairedCodeStateForRow fullRestartDelayedBothStateTestDPA .both child := by
  decide

/-- Strict-left mirror of the delayed simultaneous-close obstruction. -/
theorem fullRestartDelayedBothStateTest_left_postClose_ne_storedBoth :
    let child :=
      pairedLeftFreshChildCodeRight fullRestartDelayedBothStateTestDPA
        (false, false) fullRestartShiftedBothStateTestLeftLambda [] ((), ())
    fullRestartDelayedBothStateTestDPA.step
        (pairedCodeStateForRow fullRestartDelayedBothStateTestDPA .first child)
        (bothRoundRecord ((), ()) () ()) ≠
      pairedCodeStateForRow fullRestartDelayedBothStateTestDPA .both child := by
  decide

end DetParityAutomaton

end DistributedSynthesis
