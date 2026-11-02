/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralHeterogeneousSeamTaggedFrontCarrier
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralHeterogeneousSeamTaggedStage

/-!
# Table-retaining staged front at the exact right seam

The right seam is a homogeneous left block.  Process two therefore remains
the blind sender of the shared heterogeneous table throughout that block,
while process one remains its receiver.  The two table controls are retained
until the physical orientation reverses.

On every receive, process one refreshes a finite stage from the *current*
true-coordinate target and its stored entry row.  At the later reversal,
process one's no-receive reads this local stage and process two's receive reads
the delivered copy of the same stage.  They thereby enter the two halves of
one exact matched-right recurrent control.  No transition receives a graph,
orientation, hierarchy side, leader bit, history, or semantic view.
-/

namespace DistributedSynthesis

universe u v x y s

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

private abbrev CommonPoint :=
  ProfiledRawJointGuardedCommonSemanticPoint A strategy

private abbrev CrossValid :=
  ProfiledRawJointGuardedCommonLiteralCrossExtraValid A strategy hwin

namespace ProfiledRawJointGuardedCommonDecoratedPolicyPackage

variable {initial : CommonPoint A strategy}

private abbrev Package (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy hwin initial
    (CrossValid A strategy hwin)

private abbrev Key
    (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin package

private abbrev Installed
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package) :=
  package.literalRightSeamInstalled A strategy hwin key

private abbrev Stage
    (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamStage A strategy hwin package

/-! ## The finite receiver state retained through the left block -/

/-- Process one's left-block receiver state.  The row is stable and the exact
stage is replaced, not accumulated, on every receive.  `none` only covers the
root before the first record and malformed off-invariant table controls.

The sigma/product presentation keeps the large dependent carrier transparent
to the elaborator: key, row, table receiver, and stage are respectively
`.1`, `.2.1`, `.2.2.1`, and `.2.2.2`. -/
noncomputable abbrev
    ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState
    (package : Package A strategy hwin initial) :=
  Σ key : Key A strategy hwin package,
    PairedEntryRow ×
      (ProfiledRawJointLiteralRightBothExactReceiverState A strategy hwin
          (Installed A strategy hwin package key) ×
        Option (Stage A strategy hwin package))

noncomputable instance literalRightSeamStagedReceiverStateFintype
    (package : Package A strategy hwin initial) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A
        strategy hwin package) := by
  classical
  infer_instance

/-- The process-two state is exactly the table sender state.  In particular,
it carries neither the row nor the exact child stage. -/
abbrev ProfiledRawJointGuardedCommonLiteralRightSeamStagedSenderState
    (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamFrontSenderState A strategy hwin
    package

/-! ## Roots and same-orientation table steps -/

noncomputable def literalRightSeamStagedSenderInitial
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package) :
    ProfiledRawJointGuardedCommonLiteralRightSeamStagedSenderState A strategy
      hwin package :=
  package.literalRightSeamFrontSenderInitial A strategy hwin key

noncomputable def literalRightSeamStagedReceiverInitial
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package) (row : PairedEntryRow)
    (anchor : Bool) :
    ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A strategy
      hwin package :=
  ⟨key, row,
    profiledRawJointLiteralRightBothExactReceiverInitial A strategy hwin
      (Installed A strategy hwin package key) anchor,
    none⟩

/-- Process two advances only the shared table control. -/
noncomputable def literalRightSeamStagedSenderNoRecv
    (package : Package A strategy hwin initial)
    (state :
      ProfiledRawJointGuardedCommonLiteralRightSeamStagedSenderState A strategy
        hwin package)
    (input : In₂) : Out₂ ×
      ProfiledRawJointGuardedCommonLiteralRightSeamStagedSenderState A strategy
        hwin package :=
  package.literalRightSeamFrontSenderNoRecv A strategy hwin state input

/-- Process one advances the table receiver and refreshes the exact stage from
this record's true-coordinate target.  The previous stage is discarded. -/
noncomputable def literalRightSeamStagedReceiverRecv
    (package : Package A strategy hwin initial)
    (state :
      ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A
        strategy hwin package)
    (own : In₁) (delivered : In₂) :
    ProfiledRawJointGuardedCommonLiteralRightSeamFrontReceiverOutput A strategy
        hwin package ×
      ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A
        strategy hwin package :=
  let next := profiledRawJointLiteralRightBothExactReceiverRecv A strategy hwin
    (Installed A strategy hwin package state.1) state.2.2.1 own delivered
  let child :
      ProfiledRawJointGuardedCommonLiteralRightSeamTaggedChildCode A strategy
        hwin package :=
    ⟨state.1, next.1.2.target state.2.1⟩
  (⟨state.1, next.1⟩,
    ⟨state.1, state.2.1, next.2,
      package.literalRightSeamStageOfChild A strategy hwin state.2.1 child⟩)

@[simp] theorem literalRightSeamStagedReceiverRecv_key
    (package : Package A strategy hwin initial)
    (state :
      ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A
        strategy hwin package)
    (own : In₁) (delivered : In₂) :
    (package.literalRightSeamStagedReceiverRecv A strategy hwin state own
      delivered).2.1 = state.1 :=
  rfl

@[simp] theorem literalRightSeamStagedReceiverRecv_row
    (package : Package A strategy hwin initial)
    (state :
      ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A
        strategy hwin package)
    (own : In₁) (delivered : In₂) :
    (package.literalRightSeamStagedReceiverRecv A strategy hwin state own
      delivered).2.2.1 = state.2.1 :=
  rfl

/-- The stored stage after a receive is literally computed from the latest
output, never from the first record or the previous stage. -/
theorem literalRightSeamStagedReceiverRecv_stage
    (package : Package A strategy hwin initial)
    (state :
      ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A
        strategy hwin package)
    (own : In₁) (delivered : In₂) :
    let result := package.literalRightSeamStagedReceiverRecv A strategy hwin
      state own delivered
    result.2.2.2.2 =
      package.literalRightSeamStageOfChild A strategy hwin state.2.1
        ⟨state.1, result.1.2.2.target state.2.1⟩ :=
  rfl

/-- Whenever the current table output is identified with one semantic exact
target, the replacement refresh is the corresponding live exact stage.  This
is deliberately record-relative: `past` and `input` describe the current
record, not the first record of the block. -/
theorem literalRightSeamStagedReceiverRecv_stage_eq_exact
    (package : Package A strategy hwin initial)
    (state :
      ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A
        strategy hwin package)
    (own : In₁) (delivered : In₂)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (htarget :
      ⟨state.1,
        (package.literalRightSeamStagedReceiverRecv A strategy hwin state own
          delivered).1.2.2.target state.2.1⟩ =
        package.literalRightSeamTaggedTarget A strategy hwin state.1
          state.2.1 past input) :
    (package.literalRightSeamStagedReceiverRecv A strategy hwin state own
      delivered).2.2.2.2 =
      some (package.literalRightSeamExactStage A strategy hwin state.1
        state.2.1 past input) := by
  rw [package.literalRightSeamStagedReceiverRecv_stage A strategy hwin state
    own delivered]
  rw [htarget]
  exact package.literalRightSeamStageOfChild_exact A strategy hwin state.1
    state.2.1 past input

/-- Initially the two endpoint copies of the shared table control agree. -/
theorem literalRightSeamStaged_initial_controls_eq
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package) (row : PairedEntryRow)
    (anchor : Bool) :
    (package.literalRightSeamStagedSenderInitial A strategy hwin key).2 =
      (package.literalRightSeamStagedReceiverInitial A strategy hwin key row
        anchor).2.2.1.2.1 := by
  exact profiledRawJointLiteralRightBothExact_initial_controls_eq A strategy
    hwin (Installed A strategy hwin package key) anchor

/-- A synchronized same-orientation round preserves equality of the shared
table control. -/
theorem literalRightSeamStaged_step_controls_eq
    (package : Package A strategy hwin initial)
    (sender :
      ProfiledRawJointGuardedCommonLiteralRightSeamStagedSenderState A strategy
        hwin package)
    (receiver :
      ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A
        strategy hwin package)
    (hkey : sender.1 = receiver.1)
    (hsync : HEq sender.2 receiver.2.2.1.2.1)
    (own : In₁) (delivered : In₂) :
    HEq
      (package.literalRightSeamStagedSenderNoRecv A strategy hwin sender
        delivered).2.2
      (package.literalRightSeamStagedReceiverRecv A strategy hwin receiver own
        delivered).2.2.2.1.2.1 := by
  rcases sender with ⟨senderKey, senderControl⟩
  rcases receiver with ⟨receiverKey, row, receiverControl, stage⟩
  dsimp only at hkey
  subst receiverKey
  exact heq_of_eq
    (profiledRawJointLiteralRightBothExact_step_controls_eq A strategy hwin
      (Installed A strategy hwin package senderKey) senderControl
      receiverControl (eq_of_heq hsync) own delivered)

/-! ## Same-orientation alignment invariant -/

/-- The table sender and staged receiver denote one synchronized true-member
table state.  The exact stage is intentionally absent from this relation: it
is replaced after every receive and matters only at the later reversal. -/
def LiteralRightSeamStagedTableAligned
    (package : Package A strategy hwin initial)
    (receiver :
      ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A
        strategy hwin package)
    (sender :
      ProfiledRawJointGuardedCommonLiteralRightSeamStagedSenderState A strategy
        hwin package) : Prop :=
  sender.1 = receiver.1 ∧
    HEq sender.2 receiver.2.2.1.2.1 ∧
    receiver.2.2.1.1 = true

/-- The exact true-member roots satisfy the table alignment invariant before
the first record. -/
theorem literalRightSeamStaged_initial_aligned
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package) (row : PairedEntryRow) :
    package.LiteralRightSeamStagedTableAligned A strategy hwin
      (package.literalRightSeamStagedReceiverInitial A strategy hwin key row
        true)
      (package.literalRightSeamStagedSenderInitial A strategy hwin key) := by
  refine ⟨rfl, ?_, rfl⟩
  exact heq_of_eq
    (package.literalRightSeamStaged_initial_controls_eq A strategy hwin key row
      true)

/-- Every homogeneous left-block letter preserves alignment while refreshing
the receiver's stage to this letter's target. -/
theorem literalRightSeamStaged_leftStep_preserves
    (package : Package A strategy hwin initial)
    (receiver :
      ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A
        strategy hwin package)
    (sender :
      ProfiledRawJointGuardedCommonLiteralRightSeamStagedSenderState A strategy
        hwin package)
    (haligned : package.LiteralRightSeamStagedTableAligned A strategy hwin
      receiver sender)
    (own : In₁) (delivered : In₂) :
    package.LiteralRightSeamStagedTableAligned A strategy hwin
      (package.literalRightSeamStagedReceiverRecv A strategy hwin receiver own
        delivered).2
      (package.literalRightSeamStagedSenderNoRecv A strategy hwin sender
        delivered).2 := by
  rcases haligned with ⟨hkey, hsync, htrue⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa only [literalRightSeamFrontSenderNoRecv_key,
      literalRightSeamStagedReceiverRecv_key] using hkey
  · exact package.literalRightSeamStaged_step_controls_eq A strategy hwin
      sender receiver hkey hsync own delivered
  · simpa [literalRightSeamStagedReceiverRecv,
      profiledRawJointLiteralRightBothExactReceiverRecv] using htrue

/-! ## The pinned first record installs a live exact stage -/

/-- Execute the first table record while retaining the refreshed receiver
stage and the advanced blind table state. -/
noncomputable def literalRightSeamStagedFirstRound
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package) (row : PairedEntryRow)
    (anchor : Bool) (input : In₁ × In₂) :
    (ProfiledRawJointGuardedCommonLiteralRightSeamFrontReceiverOutput A
        strategy hwin package × Out₂) ×
      (ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A
          strategy hwin package ×
        ProfiledRawJointGuardedCommonLiteralRightSeamStagedSenderState A
          strategy hwin package) :=
  let sender := package.literalRightSeamStagedSenderNoRecv A strategy hwin
    (package.literalRightSeamStagedSenderInitial A strategy hwin key) input.2
  let receiver := package.literalRightSeamStagedReceiverRecv A strategy hwin
    (package.literalRightSeamStagedReceiverInitial A strategy hwin key row
      anchor) input.1 input.2
  ((receiver.1, sender.1), (receiver.2, sender.2))

/-- The true pinned first record stores the exact semantic stage.  This is the
reachability seed for the replacement invariant; later records refresh the
stage by the same `StageOfChild` map rather than retaining this first value. -/
theorem literalRightSeamStagedFirstRound_true_stage
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package) (row : PairedEntryRow)
    (input : In₁ × In₂) :
    let result := package.literalRightSeamStagedFirstRound A strategy hwin key
      row true input
    result.2.1.2.2.2 =
      some (package.literalRightSeamExactStage A strategy hwin key row []
        input) := by
  dsimp only [literalRightSeamStagedFirstRound,
    literalRightSeamStagedReceiverRecv,
    literalRightSeamStagedReceiverInitial,
    literalRightSeamStagedSenderNoRecv,
    literalRightSeamStagedSenderInitial,
    literalRightSeamFrontSenderNoRecv,
    literalRightSeamFrontSenderInitial]
  have htarget := package.literalRightSeamFrontTrueFirst_target A strategy hwin
    key row input
  have htag :
      ⟨key,
        (profiledRawJointLiteralRightBothExactReceiverRecv A strategy hwin
          (Installed A strategy hwin package key)
          (profiledRawJointLiteralRightBothExactReceiverInitial A strategy hwin
            (Installed A strategy hwin package key) true)
          input.1 input.2).1.2.target row⟩ =
        package.literalRightSeamTaggedTarget A strategy hwin key row []
          input := by
    simpa [literalRightSeamFrontFirstRound,
      literalRightSeamFrontReceiverRecv,
      literalRightSeamFrontReceiverInitial,
      literalRightSeamFrontSenderNoRecv,
      literalRightSeamFrontSenderInitial] using htarget
  rw [htag]
  exact package.literalRightSeamStageOfChild_exact A strategy hwin key row []
    input

/-! ## Reversal activation from the latest retained stage -/

/-- Both proof-side recurrent roots reconstructed from the currently retained
stage.  The stage is read locally by process one and through the delivered
process-one control by process two. -/
noncomputable def literalRightSeamStagedReversalMatched
    (package : Package A strategy hwin initial)
    (state :
      ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A
        strategy hwin package) :
    Option
      (ProfiledRawJointGuardedCommonLiteralRightSeamOneControl A strategy hwin
          package ×
        ProfiledRawJointGuardedCommonLiteralRightSeamTwoControl A strategy hwin
          package) :=
  state.2.2.2.map (package.literalRightSeamStageMatched A strategy hwin)

theorem literalRightSeamStagedReversalMatched_of_stage
    (package : Package A strategy hwin initial)
    (state :
      ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A
        strategy hwin package)
    (stage : Stage A strategy hwin package)
    (hstage : state.2.2.2 = some stage) :
    package.literalRightSeamStagedReversalMatched A strategy hwin state =
      some (package.literalRightSeamStageMatched A strategy hwin stage) := by
  simp [literalRightSeamStagedReversalMatched, hstage]

/-- An exact stage, regardless of when in the table block it was refreshed,
activates the exact ordinary matched pair selected by that record. -/
theorem literalRightSeamStagedReversalMatched_of_exactStage
    (package : Package A strategy hwin initial)
    (state :
      ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A
        strategy hwin package)
    (key : Key A strategy hwin package) (row : PairedEntryRow)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (hstage : state.2.2.2 =
      some (package.literalRightSeamExactStage A strategy hwin key row past
        input)) :
    package.literalRightSeamStagedReversalMatched A strategy hwin state =
      some (package.literalRightSeamTaggedMatched A strategy hwin key row past
        input) := by
  rw [package.literalRightSeamStagedReversalMatched_of_stage A strategy hwin
    state (package.literalRightSeamExactStage A strategy hwin key row past
      input) hstage]
  rw [package.literalRightSeamExactStage_matched A strategy hwin key row past
    input]

/-- Current-record alignment plus one executable receive is enough to put the
next reversal exactly at that current record's matched recurrent pair. -/
theorem literalRightSeamStagedReceiverRecv_reversalMatched_of_exact
    (package : Package A strategy hwin initial)
    (state :
      ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A
        strategy hwin package)
    (own : In₁) (delivered : In₂)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (htarget :
      ⟨state.1,
        (package.literalRightSeamStagedReceiverRecv A strategy hwin state own
          delivered).1.2.2.target state.2.1⟩ =
        package.literalRightSeamTaggedTarget A strategy hwin state.1
          state.2.1 past input) :
    package.literalRightSeamStagedReversalMatched A strategy hwin
        (package.literalRightSeamStagedReceiverRecv A strategy hwin state own
          delivered).2 =
      some (package.literalRightSeamTaggedMatched A strategy hwin state.1
        state.2.1 past input) := by
  apply package.literalRightSeamStagedReversalMatched_of_exactStage A strategy
    hwin
  exact package.literalRightSeamStagedReceiverRecv_stage_eq_exact A strategy
    hwin state own delivered past input htarget

/-- A reversal immediately after the pinned record selects the already
checked exact matched-right root pair. -/
theorem literalRightSeamStagedFirstRound_true_reversalMatched
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package) (row : PairedEntryRow)
    (input : In₁ × In₂) :
    let result := package.literalRightSeamStagedFirstRound A strategy hwin key
      row true input
    package.literalRightSeamStagedReversalMatched A strategy hwin result.2.1 =
      some (package.literalRightSeamTaggedMatched A strategy hwin key row []
        input) := by
  dsimp only
  unfold literalRightSeamStagedReversalMatched
  rw [package.literalRightSeamStagedFirstRound_true_stage A strategy hwin key
    row input]
  simp only [Option.map_some]
  rw [package.literalRightSeamExactStage_matched A strategy hwin key row []
    input]

/-- Process one's reversal no-receive starts and immediately executes the
right owner selected by its latest local stage.  `none` is the off-invariant
root fallback only. -/
noncomputable def literalRightSeamStagedReversalNoRecvOne
    (package : Package A strategy hwin initial)
    (state :
      ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A
        strategy hwin package)
    (input : In₁) : Out₁ ×
      ProfiledRawJointGuardedCommonLiteralRightSeamOneControl A strategy hwin
        package := by
  classical
  match state.2.2.2 with
  | none => exact (default, .initial ())
  | some stage =>
      let initialOne :=
        (package.literalRightSeamStageMatched A strategy hwin stage).1
      let next := package.literalRightSeamTaggedNoRecvOne A strategy hwin
        initialOne input
      exact (next.2, next.1)

/-- Process two's reversal receive reads the delivered process-one stage and
executes the matching right receiver from the same matched pair.  Its old
table sender control is intentionally irrelevant after leaving the block. -/
noncomputable def literalRightSeamStagedReversalRecvTwo
    (package : Package A strategy hwin initial)
    (_local :
      ProfiledRawJointGuardedCommonLiteralRightSeamStagedSenderState A strategy
        hwin package)
    (own : In₂)
    (delivered :
      ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A
        strategy hwin package)
    (deliveredInput : In₁) : Out₂ ×
      ProfiledRawJointGuardedCommonLiteralRightSeamTwoControl A strategy hwin
        package := by
  classical
  match delivered.2.2.2 with
  | none => exact (default, .initial ())
  | some stage =>
      let matched := package.literalRightSeamStageMatched A strategy hwin stage
      let next := package.literalRightSeamTaggedRecvTwo A strategy hwin
        matched.2 own matched.1 deliveredInput
      exact (next.2, next.1)

/-- On a live stage, the two independently executable reversal maps are
exactly the two endpoint maps of one recurrent kernel step from the same
matched-right pair. -/
theorem literalRightSeamStagedReversal_exact_pair
    (package : Package A strategy hwin initial)
    (receiver :
      ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A
        strategy hwin package)
    (sender :
      ProfiledRawJointGuardedCommonLiteralRightSeamStagedSenderState A strategy
        hwin package)
    (stage : Stage A strategy hwin package)
    (hstage : receiver.2.2.2 = some stage)
    (input : In₁ × In₂) :
    let matched := package.literalRightSeamStageMatched A strategy hwin stage
    package.literalRightSeamStagedReversalNoRecvOne A strategy hwin receiver
        input.1 =
        ((package.literalRightSeamTaggedNoRecvOne A strategy hwin matched.1
          input.1).2,
          (package.literalRightSeamTaggedNoRecvOne A strategy hwin matched.1
            input.1).1) ∧
      package.literalRightSeamStagedReversalRecvTwo A strategy hwin sender
          input.2 receiver input.1 =
        ((package.literalRightSeamTaggedRecvTwo A strategy hwin matched.2
          input.2 matched.1 input.1).2,
          (package.literalRightSeamTaggedRecvTwo A strategy hwin matched.2
            input.2 matched.1 input.1).1) := by
  dsimp only [literalRightSeamStagedReversalNoRecvOne,
    literalRightSeamStagedReversalRecvTwo]
  rw [hstage]
  constructor <;> rfl

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
