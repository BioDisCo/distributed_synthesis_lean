/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedGuardedRecurrentPhaseStep
import DistributedSynthesis.Formalizations.Lemma.LemCommittedSenderNarrowing

/-!
# Finite commitments for recurrent paired boundaries

This file instantiates the generic one-edge commitment interface at an
ordinary paired block.  A parent label commits one opposite-bank key for each
latent entry row.  The edge law checks two facts:

1. the committed key is exactly the allowed close computed by the parent
   label and monitor state; and
2. at the child label, the old block's closing output for that row equals the
   first informed output of the committed opposite bank.

The second clause is the recurrent `both`-compatibility equality isolated in
`ThmPairedGuardedRecurrentPhaseStep`.  All quantified types are finite, so
this is a decidable depth-one law and can be preserved by
`exists_transitionRational_committedNarrowed`.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-- A right block must commit the possible left target for both latent rows. -/
abbrev RightBoundaryCommitment := PairedEntryRow → BankLeftMacro A

/-- Left mirror. -/
abbrev LeftBoundaryCommitment := PairedEntryRow → BankRightMacro A

noncomputable instance : Fintype (RightBoundaryCommitment A) := by
  classical
  infer_instance

noncomputable instance : Fintype (LeftBoundaryCommitment A) := by
  classical
  infer_instance

/-! ## Right block -/

/-- The allowed target computed directly from one finite narrowed label. -/
noncomputable def stagedBankLeftFromRightLabel
    (source : BankRightMacro A)
    (monitorState : (bankRightMonitorAt A source).State)
    (label : RightNarrowedControllerLabel A (feasiblePolicy A source.1)
      source.2.1.1 source.2.1.2)
    (move : In₂ × In₁) (row : PairedEntryRow) : Option (BankLeftMacro A) := by
  classical
  let letter : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
    (move, label.2 monitorState move, label.1 move.2)
  let targetData := bankRightCloseMacro A source monitorState.2.1 row letter
  if hallowed : PairedRationalPolicy.Allowed A (feasiblePolicy A source.1)
      (Sum.inr (Sum.inl source.2.1)) (Sum.inr (Sum.inr targetData)) then
    exact some (bankStageLeftOfAllowed A source targetData hallowed)
  else
    exact none

/-- Physical first output of a freshly activated left-bank receiver. -/
noncomputable def initialBankLeftInformedOutput
    (target : BankLeftMacro A) (move : In₁ × In₂) : Out₁ :=
  (continueBankLeftReceiver A
    (initialBankLeftReceiver A target .first)
    (initialBankLeftOwner A target) move).1

/-- Concrete realization predicate consumed by committed sender narrowing. -/
def rightBoundaryCommitmentRealizes
    (source : BankRightMacro A)
    (monitorState : (bankRightMonitorAt A source).State)
    (move : In₂ × In₁)
    (parent : RightNarrowedControllerLabel A (feasiblePolicy A source.1)
      source.2.1.1 source.2.1.2)
    (commitment : RightBoundaryCommitment A)
    (nextMonitor : (bankRightMonitorAt A source).State)
    (child : RightNarrowedControllerLabel A (feasiblePolicy A source.1)
      source.2.1.1 source.2.1.2) : Prop :=
  (∀ row, stagedBankLeftFromRightLabel A source monitorState parent move row =
      some (commitment row)) ∧
    ∀ row nextMove,
      pairedRightClosingForRow row (child.2 nextMonitor nextMove) =
        initialBankLeftInformedOutput A (commitment row)
          (nextMove.2, nextMove.1)

abbrev RightCommittedNarrowedLabel (source : BankRightMacro A) :=
  CommittedNarrowedBlockLabel In₂ In₁
    (PairedRightReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂)) Out₁
    (bankRightMonitorAt A source).State (RightBoundaryCommitment A)

def rightBoundaryCommittedEdgeAllowed (source : BankRightMacro A) :=
  CommittedNarrowedEdgeAllowed
    (bankRightMonitorAt A source) (rightBoundaryCommitmentRealizes A source)

noncomputable instance (source : BankRightMacro A) :
    DecidablePred (rightBoundaryCommittedEdgeAllowed A source) := by
  classical
  infer_instance

/-- One allowed committed edge exposes the exact next-table overlap law. -/
theorem rightBoundaryCommittedEdge_output
    (source : BankRightMacro A)
    (parent child : RightCommittedNarrowedLabel A source) (inputOne : In₁)
    (hedge : rightBoundaryCommittedEdgeAllowed A source
      (parent, inputOne, child))
    (monitorState : (bankRightMonitorAt A source).State)
    (inputTwo : In₂) (row : PairedEntryRow) (nextMove : In₂ × In₁) :
    pairedRightClosingForRow row
        (child.1.2
          ((bankRightMonitorAt A source).step monitorState
            (narrowedRecord (bankRightMonitorAt A source) parent.1 monitorState
              (inputTwo, inputOne))) nextMove) =
      initialBankLeftInformedOutput A (parent.2 monitorState (inputTwo, inputOne) row)
        (nextMove.2, nextMove.1) := by
  exact (hedge monitorState inputTwo).2 row nextMove

/-- The same edge also certifies that the committed key is the parent's real
allowed close. -/
theorem rightBoundaryCommittedEdge_staged
    (source : BankRightMacro A)
    (parent child : RightCommittedNarrowedLabel A source) (inputOne : In₁)
    (hedge : rightBoundaryCommittedEdgeAllowed A source
      (parent, inputOne, child))
    (monitorState : (bankRightMonitorAt A source).State)
    (inputTwo : In₂) (row : PairedEntryRow) :
    stagedBankLeftFromRightLabel A source monitorState parent.1
        (inputTwo, inputOne) row =
      some (parent.2 monitorState (inputTwo, inputOne) row) := by
  exact (hedge monitorState inputTwo).1 row

/-- Concrete specialization of committed sender rationalization.  It leaves
only the semantic construction of a winning committed tree as input. -/
theorem exists_finite_rightBoundaryCommittedController
    (source : BankRightMacro A)
    (tree : LabeledTree In₁ (RightCommittedNarrowedLabel A source))
    (hthreads : NarrowedAllThreadsWin (bankRightMonitorAt A source)
      (forgetCommittedNarrowedTree (bankRightMonitorAt A source) tree))
    (hedges : CommittedNarrowedEdgesRealized (bankRightMonitorAt A source)
      (rightBoundaryCommitmentRealizes A source) tree) :
    ∃ controller : TransitionRationalTree.{u,
        max (max (max (max (max v u) s) (max x y)) x) s,
        max u (max (max (max (max (max v u) s) (max x y)) x) s) s} In₁
        (RightCommittedNarrowedLabel A source),
      NarrowedAllThreadsWin (bankRightMonitorAt A source)
          (forgetCommittedNarrowedTree (bankRightMonitorAt A source)
            controller.labeledTree) ∧
        CommittedNarrowedEdgesRealized (bankRightMonitorAt A source)
          (rightBoundaryCommitmentRealizes A source) controller.labeledTree := by
  classical
  letI : DecidablePred
      (CommittedNarrowedEdgeAllowed (bankRightMonitorAt A source)
        (rightBoundaryCommitmentRealizes A source)) :=
    fun edge => Classical.propDecidable
      (CommittedNarrowedEdgeAllowed (bankRightMonitorAt A source)
        (rightBoundaryCommitmentRealizes A source) edge)
  exact exists_transitionRational_committedNarrowed
    (bankRightMonitorAt A source) (rightBoundaryCommitmentRealizes A source)
    tree hthreads hedges

/-! ## Left mirror -/

noncomputable def stagedBankRightFromLeftLabel
    (source : BankLeftMacro A)
    (monitorState : (bankLeftMonitorAt A source).State)
    (label : LeftNarrowedControllerLabel A (feasiblePolicy A source.1)
      source.2.1.1 source.2.1.2)
    (move : In₁ × In₂) (row : PairedEntryRow) : Option (BankRightMacro A) := by
  classical
  let letter : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
    (move, label.2 monitorState move, label.1 move.2)
  let targetData := bankLeftCloseMacro A source monitorState.2.1 row letter
  if hallowed : PairedRationalPolicy.Allowed A (feasiblePolicy A source.1)
      (Sum.inr (Sum.inr source.2.1)) (Sum.inr (Sum.inl targetData)) then
    exact some (bankStageRightOfAllowed A source targetData hallowed)
  else
    exact none

noncomputable def initialBankRightInformedOutput
    (target : BankRightMacro A) (move : In₂ × In₁) : Out₂ :=
  (continueBankRightReceiver A
    (initialBankRightReceiver A target .first)
    (initialBankRightOwner A target) move).1

def leftBoundaryCommitmentRealizes
    (source : BankLeftMacro A)
    (monitorState : (bankLeftMonitorAt A source).State)
    (move : In₁ × In₂)
    (parent : LeftNarrowedControllerLabel A (feasiblePolicy A source.1)
      source.2.1.1 source.2.1.2)
    (commitment : LeftBoundaryCommitment A)
    (nextMonitor : (bankLeftMonitorAt A source).State)
    (child : LeftNarrowedControllerLabel A (feasiblePolicy A source.1)
      source.2.1.1 source.2.1.2) : Prop :=
  (∀ row, stagedBankRightFromLeftLabel A source monitorState parent move row =
      some (commitment row)) ∧
    ∀ row nextMove,
      pairedLeftClosingForRow row (child.2 nextMonitor nextMove) =
        initialBankRightInformedOutput A (commitment row)
          (nextMove.2, nextMove.1)

abbrev LeftCommittedNarrowedLabel (source : BankLeftMacro A) :=
  CommittedNarrowedBlockLabel In₁ In₂
    (PairedLeftReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂)) Out₂
    (bankLeftMonitorAt A source).State (LeftBoundaryCommitment A)

def leftBoundaryCommittedEdgeAllowed (source : BankLeftMacro A) :=
  CommittedNarrowedEdgeAllowed
    (bankLeftMonitorAt A source) (leftBoundaryCommitmentRealizes A source)

noncomputable instance (source : BankLeftMacro A) :
    DecidablePred (leftBoundaryCommittedEdgeAllowed A source) := by
  classical
  infer_instance

theorem leftBoundaryCommittedEdge_output
    (source : BankLeftMacro A)
    (parent child : LeftCommittedNarrowedLabel A source) (inputTwo : In₂)
    (hedge : leftBoundaryCommittedEdgeAllowed A source
      (parent, inputTwo, child))
    (monitorState : (bankLeftMonitorAt A source).State)
    (inputOne : In₁) (row : PairedEntryRow) (nextMove : In₁ × In₂) :
    pairedLeftClosingForRow row
        (child.1.2
          ((bankLeftMonitorAt A source).step monitorState
            (narrowedRecord (bankLeftMonitorAt A source) parent.1 monitorState
              (inputOne, inputTwo))) nextMove) =
      initialBankRightInformedOutput A (parent.2 monitorState (inputOne, inputTwo) row)
        (nextMove.2, nextMove.1) := by
  exact (hedge monitorState inputOne).2 row nextMove

theorem leftBoundaryCommittedEdge_staged
    (source : BankLeftMacro A)
    (parent child : LeftCommittedNarrowedLabel A source) (inputTwo : In₂)
    (hedge : leftBoundaryCommittedEdgeAllowed A source
      (parent, inputTwo, child))
    (monitorState : (bankLeftMonitorAt A source).State)
    (inputOne : In₁) (row : PairedEntryRow) :
    stagedBankRightFromLeftLabel A source monitorState parent.1
        (inputOne, inputTwo) row =
      some (parent.2 monitorState (inputOne, inputTwo) row) := by
  exact (hedge monitorState inputOne).1 row

/-- Left mirror of the finite committed-controller extraction. -/
theorem exists_finite_leftBoundaryCommittedController
    (source : BankLeftMacro A)
    (tree : LabeledTree In₂ (LeftCommittedNarrowedLabel A source))
    (hthreads : NarrowedAllThreadsWin (bankLeftMonitorAt A source)
      (forgetCommittedNarrowedTree (bankLeftMonitorAt A source) tree))
    (hedges : CommittedNarrowedEdgesRealized (bankLeftMonitorAt A source)
      (leftBoundaryCommitmentRealizes A source) tree) :
    ∃ controller : TransitionRationalTree.{v,
        max (max (max (max (max u v) s) (max x y)) y) s,
        max v (max (max (max (max (max u v) s) (max x y)) y) s) s} In₂
        (LeftCommittedNarrowedLabel A source),
      NarrowedAllThreadsWin (bankLeftMonitorAt A source)
          (forgetCommittedNarrowedTree (bankLeftMonitorAt A source)
            controller.labeledTree) ∧
        CommittedNarrowedEdgesRealized (bankLeftMonitorAt A source)
          (leftBoundaryCommitmentRealizes A source) controller.labeledTree := by
  classical
  letI : DecidablePred
      (CommittedNarrowedEdgeAllowed (bankLeftMonitorAt A source)
        (leftBoundaryCommitmentRealizes A source)) :=
    fun edge => Classical.propDecidable
      (CommittedNarrowedEdgeAllowed (bankLeftMonitorAt A source)
        (leftBoundaryCommitmentRealizes A source) edge)
  exact exists_transitionRational_committedNarrowed
    (bankLeftMonitorAt A source) (leftBoundaryCommitmentRealizes A source)
    tree hthreads hedges

end


end DetParityAutomaton

end DistributedSynthesis
