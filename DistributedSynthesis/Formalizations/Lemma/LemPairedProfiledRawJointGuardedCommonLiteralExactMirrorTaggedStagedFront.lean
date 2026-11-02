/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralExactMirrorTaggedFrontCarrier
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralExactMirrorTaggedStage

/-!
# Table-retaining staged front at the exact mirror seam

The mirror seam is a homogeneous right block.  Process one remains the blind
sender of the shared table throughout the block, while process two remains
its receiver.  On every receive, process two replaces its finite stage with
the stage read from the current true-coordinate target.  The table controls
are retained until the physical orientation reverses.

At reversal, process two starts the staged left owner locally and process one
reads the delivered stage to start the matching left receiver.  The stage is
therefore neither frozen at the first record nor accumulated.  No executable
map receives a graph, orientation, hierarchy side, leader bit, history, or
semantic view.
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
  ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin package

private abbrev Installed
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package) :=
  package.literalLeftSeamInstalled A strategy hwin key

private abbrev Stage
    (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralLeftSeamStage A strategy hwin package

/-! ## Finite states retained through the homogeneous block -/

/-- Process two retains the key, stable entry row, current table receiver,
and only the latest exact stage. -/
noncomputable abbrev
    ProfiledRawJointGuardedCommonLiteralLeftSeamStagedReceiverState
    (package : Package A strategy hwin initial) :=
  Σ key : Key A strategy hwin package,
    PairedEntryRow ×
      (ProfiledRawJointLiteralLeftBothExactReceiverState A strategy hwin
          (Installed A strategy hwin package key) ×
        Option (Stage A strategy hwin package))

noncomputable instance literalLeftSeamStagedReceiverStateFintype
    (package : Package A strategy hwin initial) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralLeftSeamStagedReceiverState A
        strategy hwin package) := by
  classical
  infer_instance

/-- Process one stays exactly the blind mirror-table sender. -/
abbrev ProfiledRawJointGuardedCommonLiteralLeftSeamStagedSenderState
    (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralLeftSeamFrontSenderState A strategy hwin
    package

/-! ## Roots and latest-stage refresh -/

noncomputable def literalLeftSeamStagedSenderInitial
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package) :
    ProfiledRawJointGuardedCommonLiteralLeftSeamStagedSenderState A strategy
      hwin package :=
  package.literalLeftSeamFrontSenderInitial A strategy hwin key

noncomputable def literalLeftSeamStagedReceiverInitial
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package) (row : PairedEntryRow)
    (anchor : Bool) :
    ProfiledRawJointGuardedCommonLiteralLeftSeamStagedReceiverState A strategy
      hwin package :=
  ⟨key, row,
    profiledRawJointLiteralLeftBothExactReceiverInitial A strategy hwin
      (Installed A strategy hwin package key) anchor,
    none⟩

/-- Process one advances only the shared mirror table. -/
noncomputable def literalLeftSeamStagedSenderNoRecv
    (package : Package A strategy hwin initial)
    (state :
      ProfiledRawJointGuardedCommonLiteralLeftSeamStagedSenderState A strategy
        hwin package)
    (input : In₁) : Out₁ ×
      ProfiledRawJointGuardedCommonLiteralLeftSeamStagedSenderState A strategy
        hwin package :=
  package.literalLeftSeamFrontSenderNoRecv A strategy hwin state input

/-- Process two advances its table receiver and replaces the stage using the
current record's exact target.  The previous stage is discarded. -/
noncomputable def literalLeftSeamStagedReceiverRecv
    (package : Package A strategy hwin initial)
    (state :
      ProfiledRawJointGuardedCommonLiteralLeftSeamStagedReceiverState A
        strategy hwin package)
    (own : In₂) (delivered : In₁) :
    ProfiledRawJointGuardedCommonLiteralLeftSeamFrontReceiverOutput A strategy
        hwin package ×
      ProfiledRawJointGuardedCommonLiteralLeftSeamStagedReceiverState A
        strategy hwin package :=
  let next := profiledRawJointLiteralLeftBothExactReceiverRecv A strategy hwin
    (Installed A strategy hwin package state.1) state.2.2.1 own delivered
  let child :
      ProfiledRawJointGuardedCommonLiteralLeftSeamTaggedChildCode A strategy
        hwin package :=
    ⟨state.1, next.1.2.target state.2.1⟩
  (⟨state.1, next.1⟩,
    ⟨state.1, state.2.1, next.2,
      package.literalLeftSeamStageOfChild A strategy hwin state.2.1 child⟩)

@[simp] theorem literalLeftSeamStagedReceiverRecv_key
    (package : Package A strategy hwin initial)
    (state :
      ProfiledRawJointGuardedCommonLiteralLeftSeamStagedReceiverState A
        strategy hwin package)
    (own : In₂) (delivered : In₁) :
    (package.literalLeftSeamStagedReceiverRecv A strategy hwin state own
      delivered).2.1 = state.1 :=
  rfl

@[simp] theorem literalLeftSeamStagedReceiverRecv_row
    (package : Package A strategy hwin initial)
    (state :
      ProfiledRawJointGuardedCommonLiteralLeftSeamStagedReceiverState A
        strategy hwin package)
    (own : In₂) (delivered : In₁) :
    (package.literalLeftSeamStagedReceiverRecv A strategy hwin state own
      delivered).2.2.1 = state.2.1 :=
  rfl

/-- The post-state stage is definitionally the stage of the latest output. -/
theorem literalLeftSeamStagedReceiverRecv_stage
    (package : Package A strategy hwin initial)
    (state :
      ProfiledRawJointGuardedCommonLiteralLeftSeamStagedReceiverState A
        strategy hwin package)
    (own : In₂) (delivered : In₁) :
    let result := package.literalLeftSeamStagedReceiverRecv A strategy hwin
      state own delivered
    result.2.2.2.2 =
      package.literalLeftSeamStageOfChild A strategy hwin state.2.1
        ⟨state.1, result.1.2.2.target state.2.1⟩ :=
  rfl

/-- Whenever the current mirror-table output is identified with one semantic
exact target, the replacement refresh is the corresponding live exact stage.
The `past` and `input` parameters describe this current record and therefore
also cover arbitrarily long homogeneous right blocks. -/
theorem literalLeftSeamStagedReceiverRecv_stage_eq_exact
    (package : Package A strategy hwin initial)
    (state :
      ProfiledRawJointGuardedCommonLiteralLeftSeamStagedReceiverState A
        strategy hwin package)
    (own : In₂) (delivered : In₁)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (htarget :
      ⟨state.1,
        (package.literalLeftSeamStagedReceiverRecv A strategy hwin state own
          delivered).1.2.2.target state.2.1⟩ =
        package.literalLeftSeamTaggedTarget A strategy hwin state.1
          state.2.1 past input) :
    (package.literalLeftSeamStagedReceiverRecv A strategy hwin state own
      delivered).2.2.2.2 =
      some (package.literalLeftSeamExactStage A strategy hwin state.1
        state.2.1 past input) := by
  rw [package.literalLeftSeamStagedReceiverRecv_stage A strategy hwin state
    own delivered]
  rw [htarget]
  exact package.literalLeftSeamStageOfChild_exact A strategy hwin state.1
    state.2.1 past input

/-- The shared table controls agree at the staged roots. -/
theorem literalLeftSeamStaged_initial_controls_eq
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package) (row : PairedEntryRow)
    (anchor : Bool) :
    (package.literalLeftSeamStagedSenderInitial A strategy hwin key).2 =
      (package.literalLeftSeamStagedReceiverInitial A strategy hwin key row
        anchor).2.2.1.2.1 := by
  exact profiledRawJointLiteralLeftBothExact_initial_controls_eq A strategy
    hwin (Installed A strategy hwin package key) anchor

/-- Same-orientation rounds preserve the shared table control even while the
receiver replaces its exact stage. -/
theorem literalLeftSeamStaged_step_controls_eq
    (package : Package A strategy hwin initial)
    (sender :
      ProfiledRawJointGuardedCommonLiteralLeftSeamStagedSenderState A strategy
        hwin package)
    (receiver :
      ProfiledRawJointGuardedCommonLiteralLeftSeamStagedReceiverState A
        strategy hwin package)
    (hkey : sender.1 = receiver.1)
    (hsync : HEq sender.2 receiver.2.2.1.2.1)
    (own : In₂) (delivered : In₁) :
    HEq
      (package.literalLeftSeamStagedSenderNoRecv A strategy hwin sender
        delivered).2.2
      (package.literalLeftSeamStagedReceiverRecv A strategy hwin receiver own
        delivered).2.2.2.1.2.1 := by
  rcases sender with ⟨senderKey, senderControl⟩
  rcases receiver with ⟨receiverKey, row, receiverControl, stage⟩
  dsimp only at hkey
  subst receiverKey
  exact heq_of_eq
    (profiledRawJointLiteralLeftBothExact_step_controls_eq A strategy hwin
      (Installed A strategy hwin package senderKey) senderControl
      receiverControl (eq_of_heq hsync) own delivered)

/-! ## The true first record seeds the replacement invariant -/

noncomputable def literalLeftSeamStagedFirstRound
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package) (row : PairedEntryRow)
    (anchor : Bool) (input : In₂ × In₁) :
    (ProfiledRawJointGuardedCommonLiteralLeftSeamFrontReceiverOutput A
        strategy hwin package × Out₁) ×
      (ProfiledRawJointGuardedCommonLiteralLeftSeamStagedReceiverState A
          strategy hwin package ×
        ProfiledRawJointGuardedCommonLiteralLeftSeamStagedSenderState A
          strategy hwin package) :=
  let sender := package.literalLeftSeamStagedSenderNoRecv A strategy hwin
    (package.literalLeftSeamStagedSenderInitial A strategy hwin key) input.2
  let receiver := package.literalLeftSeamStagedReceiverRecv A strategy hwin
    (package.literalLeftSeamStagedReceiverInitial A strategy hwin key row
      anchor) input.1 input.2
  ((receiver.1, sender.1), (receiver.2, sender.2))

/-- The pinned true record stores the exact semantic mirror stage.  Later
records use the same refresh map with their current target. -/
theorem literalLeftSeamStagedFirstRound_true_stage
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package) (row : PairedEntryRow)
    (input : In₂ × In₁) :
    let result := package.literalLeftSeamStagedFirstRound A strategy hwin key
      row true input
    result.2.1.2.2.2 =
      some (package.literalLeftSeamExactStage A strategy hwin key row []
        input) := by
  dsimp only [literalLeftSeamStagedFirstRound,
    literalLeftSeamStagedReceiverRecv,
    literalLeftSeamStagedReceiverInitial,
    literalLeftSeamStagedSenderNoRecv,
    literalLeftSeamStagedSenderInitial,
    literalLeftSeamFrontSenderNoRecv,
    literalLeftSeamFrontSenderInitial]
  have htarget := package.literalLeftSeamFrontTrueFirst_target A strategy hwin
    key row input
  have htag :
      ⟨key,
        (profiledRawJointLiteralLeftBothExactReceiverRecv A strategy hwin
          (Installed A strategy hwin package key)
          (profiledRawJointLiteralLeftBothExactReceiverInitial A strategy hwin
            (Installed A strategy hwin package key) true)
          input.1 input.2).1.2.target row⟩ =
        package.literalLeftSeamTaggedTarget A strategy hwin key row []
          input := by
    simpa [literalLeftSeamFrontFirstRound,
      literalLeftSeamFrontReceiverRecv,
      literalLeftSeamFrontReceiverInitial,
      literalLeftSeamFrontSenderNoRecv,
      literalLeftSeamFrontSenderInitial] using htarget
  rw [htag]
  exact package.literalLeftSeamStageOfChild_exact A strategy hwin key row []
    input

/-! ## Exact activation at the following reversal -/

/-- Reconstruct both recurrent roots from the receiver's latest stage. -/
noncomputable def literalLeftSeamStagedReversalMatched
    (package : Package A strategy hwin initial)
    (state :
      ProfiledRawJointGuardedCommonLiteralLeftSeamStagedReceiverState A
        strategy hwin package) :
    Option
      (ProfiledRawJointGuardedCommonLiteralLeftSeamOneControl A strategy hwin
          package ×
        ProfiledRawJointGuardedCommonLiteralLeftSeamTwoControl A strategy hwin
          package) :=
  state.2.2.2.map (package.literalLeftSeamStageMatched A strategy hwin)

theorem literalLeftSeamStagedReversalMatched_of_stage
    (package : Package A strategy hwin initial)
    (state :
      ProfiledRawJointGuardedCommonLiteralLeftSeamStagedReceiverState A
        strategy hwin package)
    (stage : Stage A strategy hwin package)
    (hstage : state.2.2.2 = some stage) :
    package.literalLeftSeamStagedReversalMatched A strategy hwin state =
      some (package.literalLeftSeamStageMatched A strategy hwin stage) := by
  simp [literalLeftSeamStagedReversalMatched, hstage]

/-- Any exact stage refreshed inside the block activates the exact
matched-left recurrent pair selected by that record. -/
theorem literalLeftSeamStagedReversalMatched_of_exactStage
    (package : Package A strategy hwin initial)
    (state :
      ProfiledRawJointGuardedCommonLiteralLeftSeamStagedReceiverState A
        strategy hwin package)
    (key : Key A strategy hwin package) (row : PairedEntryRow)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (hstage : state.2.2.2 =
      some (package.literalLeftSeamExactStage A strategy hwin key row past
        input)) :
    package.literalLeftSeamStagedReversalMatched A strategy hwin state =
      some (package.literalLeftSeamTaggedMatched A strategy hwin key row past
        input) := by
  rw [package.literalLeftSeamStagedReversalMatched_of_stage A strategy hwin
    state (package.literalLeftSeamExactStage A strategy hwin key row past
      input) hstage]
  rw [package.literalLeftSeamExactStage_matched A strategy hwin key row past
    input]

/-- Identifying one current receive output with its semantic target is enough
to make the immediately following reversal enter that current record's exact
matched-left recurrent pair. -/
theorem literalLeftSeamStagedReceiverRecv_reversalMatched_of_exact
    (package : Package A strategy hwin initial)
    (state :
      ProfiledRawJointGuardedCommonLiteralLeftSeamStagedReceiverState A
        strategy hwin package)
    (own : In₂) (delivered : In₁)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (htarget :
      ⟨state.1,
        (package.literalLeftSeamStagedReceiverRecv A strategy hwin state own
          delivered).1.2.2.target state.2.1⟩ =
        package.literalLeftSeamTaggedTarget A strategy hwin state.1
          state.2.1 past input) :
    package.literalLeftSeamStagedReversalMatched A strategy hwin
        (package.literalLeftSeamStagedReceiverRecv A strategy hwin state own
          delivered).2 =
      some (package.literalLeftSeamTaggedMatched A strategy hwin state.1
        state.2.1 past input) := by
  apply package.literalLeftSeamStagedReversalMatched_of_exactStage A strategy
    hwin
  exact package.literalLeftSeamStagedReceiverRecv_stage_eq_exact A strategy
    hwin state own delivered past input htarget

/-- Immediately after the pinned true record, reversal selects the checked
exact matched-left root pair. -/
theorem literalLeftSeamStagedFirstRound_true_reversalMatched
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package) (row : PairedEntryRow)
    (input : In₂ × In₁) :
    let result := package.literalLeftSeamStagedFirstRound A strategy hwin key
      row true input
    package.literalLeftSeamStagedReversalMatched A strategy hwin result.2.1 =
      some (package.literalLeftSeamTaggedMatched A strategy hwin key row []
        input) := by
  dsimp only
  unfold literalLeftSeamStagedReversalMatched
  rw [package.literalLeftSeamStagedFirstRound_true_stage A strategy hwin key
    row input]
  simp only [Option.map_some]
  rw [package.literalLeftSeamExactStage_matched A strategy hwin key row []
    input]

/-- At reversal process two executes the staged left owner locally. -/
noncomputable def literalLeftSeamStagedReversalNoRecvTwo
    (package : Package A strategy hwin initial)
    (state :
      ProfiledRawJointGuardedCommonLiteralLeftSeamStagedReceiverState A
        strategy hwin package)
    (input : In₂) : Out₂ ×
      ProfiledRawJointGuardedCommonLiteralLeftSeamTwoControl A strategy hwin
        package := by
  classical
  match state.2.2.2 with
  | none => exact (default, .initial ())
  | some stage =>
      let initialTwo :=
        (package.literalLeftSeamStageMatched A strategy hwin stage).2
      let next := package.literalLeftSeamTaggedNoRecvTwo A strategy hwin
        initialTwo input
      exact (next.2, next.1)

/-- At reversal process one reads the delivered process-two stage and executes
the matching left receiver.  Its old table sender state is irrelevant after
leaving the homogeneous block. -/
noncomputable def literalLeftSeamStagedReversalRecvOne
    (package : Package A strategy hwin initial)
    (_local :
      ProfiledRawJointGuardedCommonLiteralLeftSeamStagedSenderState A strategy
        hwin package)
    (own : In₁)
    (delivered :
      ProfiledRawJointGuardedCommonLiteralLeftSeamStagedReceiverState A
        strategy hwin package)
    (deliveredInput : In₂) : Out₁ ×
      ProfiledRawJointGuardedCommonLiteralLeftSeamOneControl A strategy hwin
        package := by
  classical
  match delivered.2.2.2 with
  | none => exact (default, .initial ())
  | some stage =>
      let matched := package.literalLeftSeamStageMatched A strategy hwin stage
      let next := package.literalLeftSeamTaggedRecvOne A strategy hwin
        matched.1 own matched.2 deliveredInput
      exact (next.2, next.1)

/-- With a live latest stage, both reversal maps are exactly the endpoint maps
of one recurrent step from the same matched-left pair. -/
theorem literalLeftSeamStagedReversal_exact_pair
    (package : Package A strategy hwin initial)
    (receiver :
      ProfiledRawJointGuardedCommonLiteralLeftSeamStagedReceiverState A
        strategy hwin package)
    (sender :
      ProfiledRawJointGuardedCommonLiteralLeftSeamStagedSenderState A strategy
        hwin package)
    (stage : Stage A strategy hwin package)
    (hstage : receiver.2.2.2 = some stage)
    (input : In₁ × In₂) :
    let matched := package.literalLeftSeamStageMatched A strategy hwin stage
    package.literalLeftSeamStagedReversalRecvOne A strategy hwin sender
          input.1 receiver input.2 =
        ((package.literalLeftSeamTaggedRecvOne A strategy hwin matched.1
          input.1 matched.2 input.2).2,
          (package.literalLeftSeamTaggedRecvOne A strategy hwin matched.1
            input.1 matched.2 input.2).1) ∧
      package.literalLeftSeamStagedReversalNoRecvTwo A strategy hwin receiver
          input.2 =
        ((package.literalLeftSeamTaggedNoRecvTwo A strategy hwin matched.2
          input.2).2,
          (package.literalLeftSeamTaggedNoRecvTwo A strategy hwin matched.2
            input.2).1) := by
  dsimp only [literalLeftSeamStagedReversalRecvOne,
    literalLeftSeamStagedReversalNoRecvTwo]
  rw [hstage]
  constructor <;> rfl

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
