/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemSafetyTreePositionalization
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndOperationalFamilyReceiveActivation

/-!
# The joint finite safety game of alternating family controllers

The two orientation-specific family tables cannot be selected independently:
the next right family contains one continuation of the old right table and
one continuation staged by the old left table, and conversely on the left.
This file therefore exposes the correct *joint* finite safety state.

A decision state is exactly the data visible to a receive table: both finite
summaries, each process's own preceding-round receipt bit, and both current
inputs.  It deliberately does not contain the current graph.  The receipt
bit is updated from that process's local `recv`/`noRecv` event; it is not a
strict-leader or orientation tag.  One public move chooses both family tables
at once.  Only after this common choice does the environment resolve whether
process one, process two, or both received.  Hence a positional move cannot
inspect the current orientation or a strict-leader bit, while strict and
simultaneous receives use literally the same table choice.

The remaining semantic construction has one precise target:
`EndToEndFamilyJointSafetyWitness`.  It asks the raw winning strategy for a
history-dependent tree of legal joint moves.  The generic safety
positionalization theorem then erases that proof history and returns a move
depending only on the finite receive observation.  Parity is intentionally
not folded into this game; it is carried by the fixed-policy hidden thread.
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

/-! ## Finite receive observations and joint moves -/

/-- Everything supplied to the graph-blind joint receive table.  The graph
of the current round is absent on purpose. -/
structure EndToEndFamilyReceiveObservation where
  one : EndToEndFamilyReceiptOneSummary A package
  inputOne : In₁
  two : EndToEndFamilyReceiptTwoSummary A package
  inputTwo : In₂

noncomputable instance : Fintype
    (EndToEndFamilyReceiveObservation A package) := by
  classical
  let Rep := EndToEndFamilyReceiptOneSummary A package × In₁ ×
    EndToEndFamilyReceiptTwoSummary A package × In₂
  let e : EndToEndFamilyReceiveObservation A package ≃ Rep :=
    { toFun := fun state => (state.one,
        (state.inputOne, (state.two, state.inputTwo)))
      invFun := fun state =>
        { one := state.1
          inputOne := state.2.1
          two := state.2.2.1
          inputTwo := state.2.2.2 }
      left_inv := by intro state; cases state; rfl
      right_inv := by
        intro state
        rcases state with ⟨one, ⟨inputOne, ⟨two, inputTwo⟩⟩⟩
        rfl }
  exact Fintype.ofEquiv Rep e.symm

/-- A single public move chooses both orientation tables.  Neither component
contains an actual member or a current-orientation selector. -/
abbrev EndToEndFamilyJointMove :=
  EndToEndRightFamilyPairMove A package ×
    EndToEndLeftFamilyPairMove A package

noncomputable instance : Fintype (EndToEndFamilyJointMove A package) := by
  classical
  infer_instance

/-- A branch resolves the current graph only after the joint move and also
supplies the inputs of the following decision state. -/
abbrev EndToEndFamilySafetyBranch := Graph × In₁ × In₂

noncomputable instance : Fintype (EndToEndFamilySafetyBranch
    (In₁ := In₁) (In₂ := In₂)) := by
  classical
  infer_instance

namespace EndToEndFamilyReceiveObservation

/-- The synchronized post-bank data computed without inspecting the graph.
This is exactly the computation already shared by both receive projections. -/
noncomputable def post
    (state : EndToEndFamilyReceiveObservation A package) :
    EndToEndFamilyPostBlockBanks A package :=
  endToEndFamilyPostBlockBanksOfReceiveActivate A package state.one.1
    state.inputOne state.two.1 state.inputTwo state.one.2 state.two.2

end EndToEndFamilyReceiveObservation

/-! ## The graph-blind safety transition -/

/-- The joint move is locally legal when its sources are the exact sources
read from the synchronized banks and both simultaneous tables win all their
members.  The equalities couple the two tables at one decision point; they
are not two independent existential choices. -/
def EndToEndFamilyJointMove.LegalAt
    (state : EndToEndFamilyReceiveObservation A package)
    (move : EndToEndFamilyJointMove A package) : Prop :=
  let post := state.post A package
  move.1.1 = post.rightSource A package ∧
    move.2.1 = post.leftSource A package ∧
    EndToEndRightFamilyRootTableWins A package move.1.1 move.1.2 ∧
    EndToEndLeftFamilyRootTableWins A package move.2.1 move.2.2

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- A legal joint action exists exactly when the two exact post-bank source
families are realizable.  This equivalence isolates the remaining semantic
closure obligation; there is no additional controller-choice obstruction. -/
theorem exists_endToEndFamilyJointMove_legalAt_iff
    (state : EndToEndFamilyReceiveObservation A package) :
    (∃ move : EndToEndFamilyJointMove A package,
        move.LegalAt A package state) ↔
      EndToEndRightFamilySourceRealizable A package
          ((state.post A package).rightSource A package) ∧
        EndToEndLeftFamilySourceRealizable A package
          ((state.post A package).leftSource A package) := by
  classical
  constructor
  · rintro ⟨⟨⟨rightSource, rightTable⟩, ⟨leftSource, leftTable⟩⟩,
      hrightSource, hleftSource, hrightWins, hleftWins⟩
    change rightSource = (state.post A package).rightSource A package at hrightSource
    change leftSource = (state.post A package).leftSource A package at hleftSource
    subst rightSource
    subst leftSource
    exact ⟨⟨rightTable, hrightWins⟩, ⟨leftTable, hleftWins⟩⟩
  · rintro ⟨⟨rightTable, hrightWins⟩, ⟨leftTable, hleftWins⟩⟩
    exact ⟨⟨⟨(state.post A package).rightSource A package, rightTable⟩,
        ⟨(state.post A package).leftSource A package, leftTable⟩⟩,
      rfl, rfl, hrightWins, hleftWins⟩

/-- Summary pair after resolving the current graph.  The receiver installs
its projection of the *same* joint move; a nonreceiver performs only its
ordinary blind step. -/
noncomputable def endToEndFamilyJointSafetySummaryNext
    (state : EndToEndFamilyReceiveObservation A package)
    (move : EndToEndFamilyJointMove A package) (graph : Graph) :
    EndToEndFamilyReceiptOneSummary A package ×
      EndToEndFamilyReceiptTwoSummary A package :=
  let installed :=
    (state.post A package).installSummariesRetainingWith A package move.1 move.2
  match graph with
  | .left =>
      ((installed.1, true),
        (endToEndFamilyFullStepNoRecvTwo A package state.two.1 state.inputTwo,
          false))
  | .right =>
      ((endToEndFamilyFullStepNoRecvOne A package state.one.1 state.inputOne,
          false),
        (installed.2, true))
  | .both => ((installed.1, true), (installed.2, true))

/-- One complete safety-game step.  The graph sits in the branch, hence is
resolved strictly after the move chosen from `state`. -/
noncomputable def endToEndFamilyJointSafetyNext
    (state : EndToEndFamilyReceiveObservation A package)
    (move : EndToEndFamilyJointMove A package)
    (branch : EndToEndFamilySafetyBranch (In₁ := In₁) (In₂ := In₂)) :
    EndToEndFamilyReceiveObservation A package :=
  let summaries := endToEndFamilyJointSafetySummaryNext A package state move
    branch.1
  { one := summaries.1
    inputOne := branch.2.1
    two := summaries.2
    inputTwo := branch.2.2 }

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem endToEndFamilyJointSafetySummaryNext_left
    (state : EndToEndFamilyReceiveObservation A package)
    (move : EndToEndFamilyJointMove A package) :
    endToEndFamilyJointSafetySummaryNext A package state move .left =
      ((((state.post A package).installSummariesRetainingWith A package move.1
          move.2).1, true),
        (endToEndFamilyFullStepNoRecvTwo A package state.two.1 state.inputTwo,
          false)) :=
  rfl

@[simp] theorem endToEndFamilyJointSafetySummaryNext_right
    (state : EndToEndFamilyReceiveObservation A package)
    (move : EndToEndFamilyJointMove A package) :
    endToEndFamilyJointSafetySummaryNext A package state move .right =
      ((endToEndFamilyFullStepNoRecvOne A package state.one.1 state.inputOne,
          false),
        (((state.post A package).installSummariesRetainingWith A package move.1
          move.2).2, true)) :=
  rfl

@[simp] theorem endToEndFamilyJointSafetySummaryNext_both
    (state : EndToEndFamilyReceiveObservation A package)
    (move : EndToEndFamilyJointMove A package) :
    endToEndFamilyJointSafetySummaryNext A package state move .both =
      ((((state.post A package).installSummariesRetainingWith A package move.1
          move.2).1, true),
        (((state.post A package).installSummariesRetainingWith A package move.1
          move.2).2, true)) :=
  rfl

end

/-! ## Exact local receipt updates -/

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem endToEndFamilyJointSafetySummaryNext_left_oneReceived
    (state : EndToEndFamilyReceiveObservation A package)
    (move : EndToEndFamilyJointMove A package) :
    (endToEndFamilyJointSafetySummaryNext A package state move .left).1.2 =
      true :=
  rfl

@[simp] theorem endToEndFamilyJointSafetySummaryNext_left_twoNotReceived
    (state : EndToEndFamilyReceiveObservation A package)
    (move : EndToEndFamilyJointMove A package) :
    (endToEndFamilyJointSafetySummaryNext A package state move .left).2.2 =
      false :=
  rfl

@[simp] theorem endToEndFamilyJointSafetySummaryNext_right_oneNotReceived
    (state : EndToEndFamilyReceiveObservation A package)
    (move : EndToEndFamilyJointMove A package) :
    (endToEndFamilyJointSafetySummaryNext A package state move .right).1.2 =
      false :=
  rfl

@[simp] theorem endToEndFamilyJointSafetySummaryNext_right_twoReceived
    (state : EndToEndFamilyReceiveObservation A package)
    (move : EndToEndFamilyJointMove A package) :
    (endToEndFamilyJointSafetySummaryNext A package state move .right).2.2 =
      true :=
  rfl

@[simp] theorem endToEndFamilyJointSafetySummaryNext_both_oneReceived
    (state : EndToEndFamilyReceiveObservation A package)
    (move : EndToEndFamilyJointMove A package) :
    (endToEndFamilyJointSafetySummaryNext A package state move .both).1.2 =
      true :=
  rfl

@[simp] theorem endToEndFamilyJointSafetySummaryNext_both_twoReceived
    (state : EndToEndFamilyReceiveObservation A package)
    (move : EndToEndFamilyJointMove A package) :
    (endToEndFamilyJointSafetySummaryNext A package state move .both).2.2 =
      true :=
  rfl

end

/-! ## Same-direction sender/receiver coupling -/

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- After a strict left receive, process one's retained/activated left
receiver is attached to exactly the left sender that process two keeps while
performing its blind step. -/
theorem endToEndFamilyJointSafetySummaryNext_left_moves_synchronized
    (state : EndToEndFamilyReceiveObservation A package)
    (move : EndToEndFamilyJointMove A package) :
    ((endToEndFamilyJointSafetySummaryNext A package state move .left).1.1.1).leftReceiver.2.1 =
      ((endToEndFamilyJointSafetySummaryNext A package state move .left).2.1.1).leftSender.1 := by
  change (state.post A package).leftMove = state.two.1.1.leftSender.1
  exact endToEndFamilyPostBlockBanksOfReceiveActivate_leftMove A package
    state.one.1 state.inputOne state.two.1 state.inputTwo state.one.2 state.two.2

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Right-oriented mirror. -/
theorem endToEndFamilyJointSafetySummaryNext_right_moves_synchronized
    (state : EndToEndFamilyReceiveObservation A package)
    (move : EndToEndFamilyJointMove A package) :
    ((endToEndFamilyJointSafetySummaryNext A package state move .right).2.1.1).rightReceiver.2.1 =
      ((endToEndFamilyJointSafetySummaryNext A package state move .right).1.1.1).rightSender.1 := by
  change (state.post A package).rightMove = state.one.1.1.rightSender.1
  exact endToEndFamilyPostBlockBanksOfReceiveActivate_rightMove A package
    state.one.1 state.inputOne state.two.1 state.inputTwo state.one.2 state.two.2

/-! ## Exact residual and positional extraction -/

/-- A raw semantic construction supplies a history-dependent tree of joint
legal moves.  This is the sole safety premise; in particular it does not ask
the move to depend on the current graph. -/
def EndToEndFamilyJointSafetyWitness
    (initial : EndToEndFamilyReceiveObservation A package) : Prop :=
  ∃ tree : LabeledTree
      (EndToEndFamilySafetyBranch (In₁ := In₁) (In₂ := In₂))
      (EndToEndFamilyJointMove A package),
    SafetyTreeValid initial (endToEndFamilyJointSafetyNext A package)
      (EndToEndFamilyJointMove.LegalAt A package) tree

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- The witness immediately yields a finite-state positional joint move tree.
Its move is chosen before the graph component of the next branch is read. -/
theorem exists_positionalEndToEndFamilyJointSafetyTree
    (initial : EndToEndFamilyReceiveObservation A package)
    (hwitness : EndToEndFamilyJointSafetyWitness A package initial) :
    ∃ tree : LabeledTree
        (EndToEndFamilySafetyBranch (In₁ := In₁) (In₂ := In₂))
        (EndToEndFamilyJointMove A package),
      ∀ node,
        EndToEndFamilyJointMove.LegalAt A package
          (safetyTreePositionalStateAt initial
            (endToEndFamilyJointSafetyNext A package)
            (EndToEndFamilyJointMove.LegalAt A package)
            hwitness.choose hwitness.choose_spec node).1
          (tree node) := by
  let positional := safetyTreePositionalTree initial
    (endToEndFamilyJointSafetyNext A package)
    (EndToEndFamilyJointMove.LegalAt A package)
    hwitness.choose hwitness.choose_spec
  refine ⟨positional, ?_⟩
  exact safetyTreePositionalTree_valid initial
    (endToEndFamilyJointSafetyNext A package)
    (EndToEndFamilyJointMove.LegalAt A package)
    hwitness.choose hwitness.choose_spec

end

end DetParityAutomaton

end DistributedSynthesis
