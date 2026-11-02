/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndJointSafetyGame
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndOperationalFamilyInitializer
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndPointedSourceRealizability

/-!
# A concrete winning initial boundary for the joint family game

This file separates initialization from the genuinely recurrent obligation in
the joint family game.  Pointed semantic compatibility of one exact adjacent
pair produces actual right and left family tables, not merely a proposition
saying that some tables exist.  The ordinary initializer then installs those
same tables in both sender/receiver projections of one finite observation.

The result is deliberately a *boundary* witness.  Legality at the next joint
decision additionally asks that the source families obtained after consuming
the next input pair are realizable.  That is the recurrent semantic-closure
lemma still required by `EndToEndFamilyJointSafetyWitness`; it is not hidden in
the initialization statement below.
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

/-- Exact adjacent moves together with their semantic winning proofs.  This is
the proof-carrying form of the data installed at the initial family boundary. -/
structure EndToEndAdjacentWinningFamilyMoves
    {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates) where
  moves : EndToEndAdjacentFamilyMoves A package adj
  right_wins :
    EndToEndRightFamilyRootTableWins A package
      moves.right.1 moves.right.2
  left_wins :
    EndToEndLeftFamilyRootTableWins A package
      moves.left.1 moves.left.2

/-- Pointed semantic compatibility chooses concrete winning tables for both
orientation families.  The selectors are applied once to the exact adjacent
source maps; no member, current orientation, or strict-leader bit is exposed. -/
noncomputable def endToEndAdjacentWinningFamilyMovesOfPointed
    {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates)
    (hcompatible : adj.PointedSemanticCompatible A package) :
    EndToEndAdjacentWinningFamilyMoves A package adj := by
  let right := endToEndRightFamilyMoveSelector A package
    (adj.rightFamilySource A package)
  let left := endToEndLeftFamilyMoveSelector A package
    (adj.leftFamilySource A package)
  have hwins :=
    adj.familyMoveSelectors_win_of_pointedSemanticCompatible A package
      hcompatible
  exact
    { moves :=
        { right := right
          left := left
          right_source := rfl
          left_source := rfl }
      right_wins := hwins.1
      left_wins := hwins.2 }

/-- Turn initialized controls into the first finite receive observation.  The
two receipt bits are the processes' own preceding-round observations. -/
def initialEndToEndFamilyReceiveObservationOfAdjacency
    {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates)
    (historicalAnchor receivedOne receivedTwo : Bool)
    (moves : EndToEndAdjacentFamilyMoves A package adj)
    (outputOne : Out₁) (inputOne : In₁)
    (outputTwo : Out₂) (inputTwo : In₂) :
    EndToEndFamilyReceiveObservation A package :=
  let controls := initialEndToEndFamilyControlsOfAdjacency A package adj
    historicalAnchor receivedOne receivedTwo moves
  { one := ((controls.one, outputOne), receivedOne)
    inputOne := inputOne
    two := ((controls.two, outputTwo), receivedTwo)
    inputTwo := inputTwo }

@[simp] theorem initialEndToEndFamilyReceiveObservation_receivedOne
    {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates)
    (historicalAnchor receivedOne receivedTwo : Bool)
    (moves : EndToEndAdjacentFamilyMoves A package adj)
    (outputOne : Out₁) (inputOne : In₁)
    (outputTwo : Out₂) (inputTwo : In₂) :
    (initialEndToEndFamilyReceiveObservationOfAdjacency A package adj
      historicalAnchor receivedOne receivedTwo moves outputOne inputOne
      outputTwo inputTwo).one.2 = receivedOne :=
  rfl

@[simp] theorem initialEndToEndFamilyReceiveObservation_receivedTwo
    {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates)
    (historicalAnchor receivedOne receivedTwo : Bool)
    (moves : EndToEndAdjacentFamilyMoves A package adj)
    (outputOne : Out₁) (inputOne : In₁)
    (outputTwo : Out₂) (inputTwo : In₂) :
    (initialEndToEndFamilyReceiveObservationOfAdjacency A package adj
      historicalAnchor receivedOne receivedTwo moves outputOne inputOne
      outputTwo inputTwo).two.2 = receivedTwo :=
  rfl

/-- The initial process-one sender contains the literal winning right table
selected for the adjacent source family. -/
theorem initialEndToEndFamilyReceiveObservation_rightSender_wins
    {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates)
    (historicalAnchor receivedOne receivedTwo : Bool)
    (winning : EndToEndAdjacentWinningFamilyMoves A package adj)
    (outputOne : Out₁) (inputOne : In₁)
    (outputTwo : Out₂) (inputTwo : In₂) :
    let initial := initialEndToEndFamilyReceiveObservationOfAdjacency A package
      adj historicalAnchor receivedOne receivedTwo winning.moves outputOne
      inputOne outputTwo inputTwo
    EndToEndRightFamilyRootTableWins A package
      initial.one.1.1.rightSender.1.1
      initial.one.1.1.rightSender.1.2 := by
  dsimp only [initialEndToEndFamilyReceiveObservationOfAdjacency]
  exact winning.right_wins

/-- Left-family mirror. -/
theorem initialEndToEndFamilyReceiveObservation_leftSender_wins
    {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates)
    (historicalAnchor receivedOne receivedTwo : Bool)
    (winning : EndToEndAdjacentWinningFamilyMoves A package adj)
    (outputOne : Out₁) (inputOne : In₁)
    (outputTwo : Out₂) (inputTwo : In₂) :
    let initial := initialEndToEndFamilyReceiveObservationOfAdjacency A package
      adj historicalAnchor receivedOne receivedTwo winning.moves outputOne
      inputOne outputTwo inputTwo
    EndToEndLeftFamilyRootTableWins A package
      initial.two.1.1.leftSender.1.1
      initial.two.1.1.leftSender.1.2 := by
  dsimp only [initialEndToEndFamilyReceiveObservationOfAdjacency]
  exact winning.left_wins

/-- Initialization nonemptiness in executable form: from one semantically
compatible adjacent pair we return the finite receive observation and the two
literal winning tables stored in it. -/
theorem exists_initialEndToEndFamilyReceiveObservation_with_winningBoundary
    {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates)
    (hcompatible : adj.PointedSemanticCompatible A package)
    (historicalAnchor receivedOne receivedTwo : Bool)
    (outputOne : Out₁) (inputOne : In₁)
    (outputTwo : Out₂) (inputTwo : In₂) :
    ∃ initial : EndToEndFamilyReceiveObservation A package,
      initial.one.2 = receivedOne ∧
      initial.two.2 = receivedTwo ∧
      initial.one.1.1.rightSender.1.1 = adj.rightFamilySource A package ∧
      initial.two.1.1.leftSender.1.1 = adj.leftFamilySource A package ∧
      EndToEndRightFamilyRootTableWins A package
        initial.one.1.1.rightSender.1.1
        initial.one.1.1.rightSender.1.2 ∧
      EndToEndLeftFamilyRootTableWins A package
        initial.two.1.1.leftSender.1.1
        initial.two.1.1.leftSender.1.2 := by
  let winning := endToEndAdjacentWinningFamilyMovesOfPointed A package adj
    hcompatible
  let initial := initialEndToEndFamilyReceiveObservationOfAdjacency A package
    adj historicalAnchor receivedOne receivedTwo winning.moves outputOne
    inputOne outputTwo inputTwo
  refine ⟨initial, rfl, rfl, winning.moves.right_source,
    winning.moves.left_source, ?_, ?_⟩
  · exact initialEndToEndFamilyReceiveObservation_rightSender_wins A package
      adj historicalAnchor receivedOne receivedTwo winning outputOne inputOne
      outputTwo inputTwo
  · exact initialEndToEndFamilyReceiveObservation_leftSender_wins A package
      adj historicalAnchor receivedOne receivedTwo winning outputOne inputOne
      outputTwo inputTwo

end

end DetParityAutomaton

end DistributedSynthesis
