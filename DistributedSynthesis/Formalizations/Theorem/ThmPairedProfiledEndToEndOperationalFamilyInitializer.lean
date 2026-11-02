/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndOperationalAdjacency
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndOperationalFamilyReceiverBank

/-!
# Installing an exact adjacent family at the runtime boundary

This file is deliberately downstream of table construction.  It receives one
right family move and one left family move whose source maps are the exact
mixed restart roots extracted from an `EndToEndBothPendingAdjacency`; it does
not choose or rationalize either table.

The blind sender halves start at the shared family-table controls.  The dual
receiver halves retain both member states.  Member `false` starts from the
current phase and therefore keeps its exact entry row; member `true` starts
from the staged opposite root and receives the row encoded by the bank
owner's own previous-receipt bit.  The common historical anchor is stored in
both receiver bundles, but it selects different physical members: the right
bank uses `anchor`, while the left bank uses `!anchor`.  None of these data is
the current graph, an orientation selector, or a leader signal.
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

/-! ## Exact rows retained by the six adjacency witnesses -/

namespace EndToEndRightPendingAdjacency

/-- Entry row of the current right phase. -/
def row {phase : EndToEndMatchedPhase A package}
    (adj : EndToEndRightPendingAdjacency A package phase) : PairedEntryRow :=
  match adj with
  | .first _ row _ _ _ => row
  | .rightOrigin _ _ _ row _ _ _ => row
  | .leftOrigin _ _ _ row _ _ _ => row

end EndToEndRightPendingAdjacency

namespace EndToEndLeftPendingAdjacency

/-- Entry row of the current left phase. -/
def row {phase : EndToEndMatchedPhase A package}
    (adj : EndToEndLeftPendingAdjacency A package phase) : PairedEntryRow :=
  match adj with
  | .first _ row _ _ _ => row
  | .rightOrigin _ _ _ row _ _ _ => row
  | .leftOrigin _ _ _ row _ _ _ => row

end EndToEndLeftPendingAdjacency

namespace EndToEndBothPendingAdjacency

/-- Rows for the right-family receiver bank.  The current member retains its
row; the staged member starts at the row determined by the historical receipt
bit used at its reversal boundary. -/
def rightFamilyRows {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates)
    (receivedTwo : Bool) : Bool → PairedEntryRow
  | false => adj.right.row A package
  | true => guardedEntryRowOfReceived receivedTwo

/-- Left-family mirror. -/
def leftFamilyRows {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates)
    (receivedOne : Bool) : Bool → PairedEntryRow
  | false => adj.left.row A package
  | true => guardedEntryRowOfReceived receivedOne

@[simp] theorem rightFamilyRows_false
    {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates)
    (receivedTwo : Bool) :
    adj.rightFamilyRows A package receivedTwo false =
      adj.right.row A package := rfl

@[simp] theorem rightFamilyRows_true
    {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates)
    (receivedTwo : Bool) :
    adj.rightFamilyRows A package receivedTwo true =
      guardedEntryRowOfReceived receivedTwo := rfl

@[simp] theorem leftFamilyRows_false
    {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates)
    (receivedOne : Bool) :
    adj.leftFamilyRows A package receivedOne false =
      adj.left.row A package := rfl

@[simp] theorem leftFamilyRows_true
    {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates)
    (receivedOne : Bool) :
    adj.leftFamilyRows A package receivedOne true =
      guardedEntryRowOfReceived receivedOne := rfl

end EndToEndBothPendingAdjacency

/-! ## Supplied tables with exact source maps -/

/-- The proof-only installation witness.  The runtime controls retain the two
moves but erase both equalities. -/
structure EndToEndAdjacentFamilyMoves
    {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates) where
  right : EndToEndRightFamilyPairMove A package
  left : EndToEndLeftFamilyPairMove A package
  right_source : right.1 = adj.rightFamilySource A package
  left_source : left.1 = adj.leftFamilySource A package

/-- Both actual local controls installed at one synchronized family boundary. -/
structure EndToEndInitializedFamilyControls where
  one : EndToEndFamilyFullOneControl A package
  two : EndToEndFamilyFullTwoControl A package

/-! The synchronized provenance anchor has opposite family coordinates at the
two receivers.  These definitions expose that convention without storing a
current orientation or asking either process which side is informed. -/

/-- Physical right-family member justified by the common past anchor. -/
def endToEndRightPhysicalFamilyMember (historicalAnchor : Bool) : Bool :=
  historicalAnchor

/-- Physical left-family member justified by the same past anchor. -/
def endToEndLeftPhysicalFamilyMember (historicalAnchor : Bool) : Bool :=
  !historicalAnchor

@[simp] theorem endToEndRightPhysicalFamilyMember_eq
    (historicalAnchor : Bool) :
    endToEndRightPhysicalFamilyMember historicalAnchor = historicalAnchor :=
  rfl

@[simp] theorem endToEndLeftPhysicalFamilyMember_eq
    (historicalAnchor : Bool) :
    endToEndLeftPhysicalFamilyMember historicalAnchor = !historicalAnchor :=
  rfl

theorem endToEndLeftPhysicalFamilyMember_eq_not_right
    (historicalAnchor : Bool) :
    endToEndLeftPhysicalFamilyMember historicalAnchor =
      !endToEndRightPhysicalFamilyMember historicalAnchor :=
  rfl

/-- Install the two supplied tables and both dual receiver banks. -/
def initialEndToEndFamilyControlsOfAdjacency
    {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates)
    (historicalAnchor receivedOne receivedTwo : Bool)
    (moves : EndToEndAdjacentFamilyMoves A package adj) :
    EndToEndInitializedFamilyControls A package :=
  { one :=
      { rightSender :=
          EndToEndRightFamilyPairOverlay.initial A package moves.right
        leftReceiver :=
          (historicalAnchor, ⟨moves.left,
            initialEndToEndLeftFamilyReceiverBank A package moves.left
              (adj.leftFamilyRows A package receivedOne)⟩) }
    two :=
      { rightReceiver :=
          (historicalAnchor, ⟨moves.right,
            initialEndToEndRightFamilyReceiverBank A package moves.right
              (adj.rightFamilyRows A package receivedTwo)⟩)
        leftSender :=
          EndToEndLeftFamilyPairOverlay.initial A package moves.left } }

/-! ## Top-level projection equations -/

@[simp] theorem initialEndToEndFamilyControls_rightSender_move
    {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates)
    (historicalAnchor receivedOne receivedTwo : Bool)
    (moves : EndToEndAdjacentFamilyMoves A package adj) :
    (initialEndToEndFamilyControlsOfAdjacency A package adj historicalAnchor receivedOne receivedTwo
      moves).one.rightSender.1 = moves.right := rfl

@[simp] theorem initialEndToEndFamilyControls_leftSender_move
    {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates)
    (historicalAnchor receivedOne receivedTwo : Bool)
    (moves : EndToEndAdjacentFamilyMoves A package adj) :
    (initialEndToEndFamilyControlsOfAdjacency A package adj historicalAnchor receivedOne receivedTwo
      moves).two.leftSender.1 = moves.left := rfl

@[simp] theorem initialEndToEndFamilyControls_leftReceiver_anchor
    {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates)
    (historicalAnchor receivedOne receivedTwo : Bool)
    (moves : EndToEndAdjacentFamilyMoves A package adj) :
    (initialEndToEndFamilyControlsOfAdjacency A package adj historicalAnchor receivedOne receivedTwo
      moves).one.leftReceiver.1 = historicalAnchor := rfl

@[simp] theorem initialEndToEndFamilyControls_rightReceiver_anchor
    {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates)
    (historicalAnchor receivedOne receivedTwo : Bool)
    (moves : EndToEndAdjacentFamilyMoves A package adj) :
    (initialEndToEndFamilyControlsOfAdjacency A package adj historicalAnchor receivedOne receivedTwo
      moves).two.rightReceiver.1 = historicalAnchor := rfl

@[simp] theorem initialEndToEndFamilyControls_leftReceiver_move
    {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates)
    (historicalAnchor receivedOne receivedTwo : Bool)
    (moves : EndToEndAdjacentFamilyMoves A package adj) :
    (initialEndToEndFamilyControlsOfAdjacency A package adj historicalAnchor receivedOne receivedTwo
      moves).one.leftReceiver.2.1 = moves.left := rfl

@[simp] theorem initialEndToEndFamilyControls_rightReceiver_move
    {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates)
    (historicalAnchor receivedOne receivedTwo : Bool)
    (moves : EndToEndAdjacentFamilyMoves A package adj) :
    (initialEndToEndFamilyControlsOfAdjacency A package adj historicalAnchor receivedOne receivedTwo
      moves).two.rightReceiver.2.1 = moves.right := rfl

/-! ## Memberwise source and receiver-root equations -/

theorem initialEndToEndFamilyControls_rightSender_root
    {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates)
    (historicalAnchor receivedOne receivedTwo : Bool)
    (moves : EndToEndAdjacentFamilyMoves A package adj) (member : Bool) :
    (initialEndToEndFamilyControlsOfAdjacency A package adj historicalAnchor receivedOne receivedTwo
      moves).one.rightSender.1.1 member =
        adj.rightFamilySource A package member := by
  exact congrFun moves.right_source member

theorem initialEndToEndFamilyControls_leftSender_root
    {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates)
    (historicalAnchor receivedOne receivedTwo : Bool)
    (moves : EndToEndAdjacentFamilyMoves A package adj) (member : Bool) :
    (initialEndToEndFamilyControlsOfAdjacency A package adj historicalAnchor receivedOne receivedTwo
      moves).two.leftSender.1.1 member =
        adj.leftFamilySource A package member := by
  exact congrFun moves.left_source member

theorem initialEndToEndFamilyControls_rightReceiver_root
    {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates)
    (historicalAnchor receivedOne receivedTwo : Bool)
    (moves : EndToEndAdjacentFamilyMoves A package adj) (member : Bool) :
    (initialEndToEndFamilyControlsOfAdjacency A package adj historicalAnchor receivedOne receivedTwo
      moves).two.rightReceiver.2.1.1 member =
        adj.rightFamilySource A package member := by
  exact congrFun moves.right_source member

theorem initialEndToEndFamilyControls_leftReceiver_root
    {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates)
    (historicalAnchor receivedOne receivedTwo : Bool)
    (moves : EndToEndAdjacentFamilyMoves A package adj) (member : Bool) :
    (initialEndToEndFamilyControlsOfAdjacency A package adj historicalAnchor receivedOne receivedTwo
      moves).one.leftReceiver.2.1.1 member =
        adj.leftFamilySource A package member := by
  exact congrFun moves.left_source member

/-- Source-constructor projections follow from the whole dependent-root
equations, without transporting monitor states separately. -/
theorem initialEndToEndFamilyControls_rightReceiver_source
    {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates)
    (historicalAnchor receivedOne receivedTwo : Bool)
    (moves : EndToEndAdjacentFamilyMoves A package adj) (member : Bool) :
    ((initialEndToEndFamilyControlsOfAdjacency A package adj historicalAnchor receivedOne receivedTwo
      moves).two.rightReceiver.2.1.1 member).1 =
        (adj.rightFamilySource A package member).1 := by
  exact congrArg Sigma.fst
    (initialEndToEndFamilyControls_rightReceiver_root A package adj
      historicalAnchor receivedOne receivedTwo moves member)

theorem initialEndToEndFamilyControls_leftReceiver_source
    {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates)
    (historicalAnchor receivedOne receivedTwo : Bool)
    (moves : EndToEndAdjacentFamilyMoves A package adj) (member : Bool) :
    ((initialEndToEndFamilyControlsOfAdjacency A package adj historicalAnchor receivedOne receivedTwo
      moves).one.leftReceiver.2.1.1 member).1 =
        (adj.leftFamilySource A package member).1 := by
  exact congrArg Sigma.fst
    (initialEndToEndFamilyControls_leftReceiver_root A package adj
      historicalAnchor receivedOne receivedTwo moves member)

/-! ## The alternating physical projections

The bank equations above hold for every proof-side member.  At runtime the
right receiver reads member `historicalAnchor`, whereas the left receiver
reads member `!historicalAnchor`.  The following equations keep that crossing
visible at the seam. -/

theorem initialEndToEndFamilyControls_rightReceiver_physicalRoot
    {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates)
    (historicalAnchor receivedOne receivedTwo : Bool)
    (moves : EndToEndAdjacentFamilyMoves A package adj) :
    (initialEndToEndFamilyControlsOfAdjacency A package adj historicalAnchor
      receivedOne receivedTwo moves).two.rightReceiver.2.1.1
        (endToEndRightPhysicalFamilyMember historicalAnchor) =
      adj.rightFamilySource A package historicalAnchor := by
  simpa using initialEndToEndFamilyControls_rightReceiver_root A package adj
    historicalAnchor receivedOne receivedTwo moves historicalAnchor

theorem initialEndToEndFamilyControls_leftReceiver_physicalRoot
    {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates)
    (historicalAnchor receivedOne receivedTwo : Bool)
    (moves : EndToEndAdjacentFamilyMoves A package adj) :
    (initialEndToEndFamilyControlsOfAdjacency A package adj historicalAnchor
      receivedOne receivedTwo moves).one.leftReceiver.2.1.1
        (endToEndLeftPhysicalFamilyMember historicalAnchor) =
      adj.leftFamilySource A package (!historicalAnchor) := by
  simpa using initialEndToEndFamilyControls_leftReceiver_root A package adj
    historicalAnchor receivedOne receivedTwo moves (!historicalAnchor)

/-- The two possible anchor values expose the actual alternation: at `false`
the physical roots are current-right/pending-left, while at `true` they are
pending-right/current-left. -/
theorem initialEndToEndFamilyControls_physicalReceiverRoots
    {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates)
    (historicalAnchor receivedOne receivedTwo : Bool)
    (moves : EndToEndAdjacentFamilyMoves A package adj) :
    ((initialEndToEndFamilyControlsOfAdjacency A package adj historicalAnchor
        receivedOne receivedTwo moves).two.rightReceiver.2.1.1
          (endToEndRightPhysicalFamilyMember historicalAnchor),
      (initialEndToEndFamilyControlsOfAdjacency A package adj historicalAnchor
        receivedOne receivedTwo moves).one.leftReceiver.2.1.1
          (endToEndLeftPhysicalFamilyMember historicalAnchor)) =
      if historicalAnchor then
        (adj.left.pendingRoot A package, adj.left.currentRoot A package)
      else
        (adj.right.currentRoot A package, adj.right.pendingRoot A package) := by
  cases historicalAnchor
  · apply Prod.ext
    · simpa using initialEndToEndFamilyControls_rightReceiver_root A package
        adj false receivedOne receivedTwo moves false
    · simpa using initialEndToEndFamilyControls_leftReceiver_root A package
        adj false receivedOne receivedTwo moves true
  · apply Prod.ext
    · simpa using initialEndToEndFamilyControls_rightReceiver_root A package
        adj true receivedOne receivedTwo moves true
    · simpa using initialEndToEndFamilyControls_leftReceiver_root A package
        adj true receivedOne receivedTwo moves false

@[simp] theorem initialEndToEndFamilyControls_rightSender_root_false
    {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates)
    (historicalAnchor receivedOne receivedTwo : Bool)
    (moves : EndToEndAdjacentFamilyMoves A package adj) :
    (initialEndToEndFamilyControlsOfAdjacency A package adj historicalAnchor receivedOne receivedTwo
      moves).one.rightSender.1.1 false =
        adj.right.currentRoot A package := by
  simpa using initialEndToEndFamilyControls_rightSender_root A package adj
    historicalAnchor receivedOne receivedTwo moves false

@[simp] theorem initialEndToEndFamilyControls_rightSender_root_true
    {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates)
    (historicalAnchor receivedOne receivedTwo : Bool)
    (moves : EndToEndAdjacentFamilyMoves A package adj) :
    (initialEndToEndFamilyControlsOfAdjacency A package adj historicalAnchor receivedOne receivedTwo
      moves).one.rightSender.1.1 true =
        adj.left.pendingRoot A package := by
  simpa using initialEndToEndFamilyControls_rightSender_root A package adj
    historicalAnchor receivedOne receivedTwo moves true

@[simp] theorem initialEndToEndFamilyControls_leftSender_root_false
    {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates)
    (historicalAnchor receivedOne receivedTwo : Bool)
    (moves : EndToEndAdjacentFamilyMoves A package adj) :
    (initialEndToEndFamilyControlsOfAdjacency A package adj historicalAnchor receivedOne receivedTwo
      moves).two.leftSender.1.1 false =
        adj.left.currentRoot A package := by
  simpa using initialEndToEndFamilyControls_leftSender_root A package adj
    historicalAnchor receivedOne receivedTwo moves false

@[simp] theorem initialEndToEndFamilyControls_leftSender_root_true
    {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates)
    (historicalAnchor receivedOne receivedTwo : Bool)
    (moves : EndToEndAdjacentFamilyMoves A package adj) :
    (initialEndToEndFamilyControlsOfAdjacency A package adj historicalAnchor receivedOne receivedTwo
      moves).two.leftSender.1.1 true =
        adj.right.pendingRoot A package := by
  simpa using initialEndToEndFamilyControls_leftSender_root A package adj
    historicalAnchor receivedOne receivedTwo moves true

/-! The shared sender state is the initial control of every proof-side member
projection.  These are the exact projection equations later consumed by the
member-step correspondence. -/

theorem initialEndToEndFamilyControls_rightSender_memberControl
    {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates)
    (historicalAnchor receivedOne receivedTwo : Bool)
    (moves : EndToEndAdjacentFamilyMoves A package adj) (member : Bool) :
    let sender :=
    (initialEndToEndFamilyControlsOfAdjacency A package adj historicalAnchor receivedOne receivedTwo
        moves).one.rightSender
    sender.2.memberControl
        (endToEndRightFamilyRootMonitors A package sender.1.1)
        sender.1.2.toTransitionRationalTree member =
      (finiteRootMemberController
        (endToEndRightFamilyRootMonitors A package sender.1.1)
        sender.1.2.toTransitionRationalTree member).initial := by
  rfl

theorem initialEndToEndFamilyControls_leftSender_memberControl
    {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates)
    (historicalAnchor receivedOne receivedTwo : Bool)
    (moves : EndToEndAdjacentFamilyMoves A package adj) (member : Bool) :
    let sender :=
    (initialEndToEndFamilyControlsOfAdjacency A package adj historicalAnchor receivedOne receivedTwo
        moves).two.leftSender
    sender.2.memberControl
        (endToEndLeftFamilyRootMonitors A package sender.1.1)
        sender.1.2.toTransitionRationalTree member =
      (finiteRootMemberController
        (endToEndLeftFamilyRootMonitors A package sender.1.1)
        sender.1.2.toTransitionRationalTree member).initial := by
  rfl

/-! ## Exact dual-bank initialization -/

@[simp] theorem initialEndToEndFamilyControls_rightReceiver_row
    {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates)
    (historicalAnchor receivedOne receivedTwo : Bool)
    (moves : EndToEndAdjacentFamilyMoves A package adj) (member : Bool) :
    ((initialEndToEndFamilyControlsOfAdjacency A package adj historicalAnchor receivedOne receivedTwo
      moves).two.rightReceiver.2.2 member).1 =
        adj.rightFamilyRows A package receivedTwo member := rfl

@[simp] theorem initialEndToEndFamilyControls_leftReceiver_row
    {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates)
    (historicalAnchor receivedOne receivedTwo : Bool)
    (moves : EndToEndAdjacentFamilyMoves A package adj) (member : Bool) :
    ((initialEndToEndFamilyControlsOfAdjacency A package adj historicalAnchor receivedOne receivedTwo
      moves).one.leftReceiver.2.2 member).1 =
        adj.leftFamilyRows A package receivedOne member := rfl

@[simp] theorem initialEndToEndFamilyControls_rightReceiver_pending
    {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates)
    (historicalAnchor receivedOne receivedTwo : Bool)
    (moves : EndToEndAdjacentFamilyMoves A package adj) (member : Bool) :
    ((initialEndToEndFamilyControlsOfAdjacency A package adj historicalAnchor receivedOne receivedTwo
      moves).two.rightReceiver.2.2 member).2.2 = none := rfl

@[simp] theorem initialEndToEndFamilyControls_leftReceiver_pending
    {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates)
    (historicalAnchor receivedOne receivedTwo : Bool)
    (moves : EndToEndAdjacentFamilyMoves A package adj) (member : Bool) :
    ((initialEndToEndFamilyControlsOfAdjacency A package adj historicalAnchor receivedOne receivedTwo
      moves).one.leftReceiver.2.2 member).2.2 = none := rfl

/-- Coordinate-wise, member `false` in each bank retains its exact current
phase row.  The two physical members selected by one anchor are generally not
both `false`; see the alternating projections below. -/
@[simp] theorem initialEndToEndFamilyControls_rightReceiver_currentRow
    {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates)
    (historicalAnchor receivedOne receivedTwo : Bool)
    (moves : EndToEndAdjacentFamilyMoves A package adj) :
    ((initialEndToEndFamilyControlsOfAdjacency A package adj historicalAnchor receivedOne receivedTwo
      moves).two.rightReceiver.2.2 false).1 = adj.right.row A package := rfl

@[simp] theorem initialEndToEndFamilyControls_leftReceiver_currentRow
    {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates)
    (historicalAnchor receivedOne receivedTwo : Bool)
    (moves : EndToEndAdjacentFamilyMoves A package adj) :
    ((initialEndToEndFamilyControlsOfAdjacency A package adj historicalAnchor receivedOne receivedTwo
      moves).one.leftReceiver.2.2 false).1 = adj.left.row A package := rfl

/-- Coordinate-wise, member `true` starts with the bank owner's own previous-
receipt row used by the strict-reversal constructor. -/
@[simp] theorem initialEndToEndFamilyControls_rightReceiver_stagedRow
    {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates)
    (historicalAnchor receivedOne receivedTwo : Bool)
    (moves : EndToEndAdjacentFamilyMoves A package adj) :
    ((initialEndToEndFamilyControlsOfAdjacency A package adj historicalAnchor receivedOne receivedTwo
      moves).two.rightReceiver.2.2 true).1 =
        guardedEntryRowOfReceived receivedTwo := rfl

@[simp] theorem initialEndToEndFamilyControls_leftReceiver_stagedRow
    {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates)
    (historicalAnchor receivedOne receivedTwo : Bool)
    (moves : EndToEndAdjacentFamilyMoves A package adj) :
    ((initialEndToEndFamilyControlsOfAdjacency A package adj historicalAnchor receivedOne receivedTwo
      moves).one.leftReceiver.2.2 true).1 =
        guardedEntryRowOfReceived receivedOne := rfl

/-- The physical rows follow the same crossed member convention as the roots.
The staged right row uses process two's local receipt bit, and the staged left
row uses process one's; the common anchor is used only to choose coordinates. -/
theorem initialEndToEndFamilyControls_physicalReceiverRows
    {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates)
    (historicalAnchor receivedOne receivedTwo : Bool)
    (moves : EndToEndAdjacentFamilyMoves A package adj) :
    (((initialEndToEndFamilyControlsOfAdjacency A package adj historicalAnchor
        receivedOne receivedTwo moves).two.rightReceiver.2.2
          (endToEndRightPhysicalFamilyMember historicalAnchor)).1,
      ((initialEndToEndFamilyControlsOfAdjacency A package adj historicalAnchor
        receivedOne receivedTwo moves).one.leftReceiver.2.2
          (endToEndLeftPhysicalFamilyMember historicalAnchor)).1) =
      if historicalAnchor then
        (guardedEntryRowOfReceived receivedTwo, adj.left.row A package)
      else
        (adj.right.row A package, guardedEntryRowOfReceived receivedOne) := by
  cases historicalAnchor <;> rfl

end

end DetParityAutomaton

end DistributedSynthesis
