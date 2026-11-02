/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralBranchAwareStageLiveness

/-!
# Fresh-row restarted literal seam stages

A strict close reads its target from the checker row before the close, but the
resulting one-sided block starts in the fresh `.first` row.  The older staged
front used one row for both roles.  This module keeps the old transition
available and adds the restarted transition needed by physical checker
alignment.
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

private abbrev Package :=
  ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy hwin initial
    (CrossValid A strategy hwin)

/-! ## Right seam -/

/-- Branch-aware receive that reads the semantic target at the retained
source row and installs the resulting strict block at fresh row `.first`. -/
noncomputable def literalRightSeamBranchRestartedReceiverRecv
    (package : Package A strategy hwin (initial := initial))
    (state :
      ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A
        strategy hwin package)
    (own : In₁) (delivered : In₂) :
    ProfiledRawJointGuardedCommonLiteralRightSeamFrontReceiverOutput A strategy
        hwin package ×
      ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A
        strategy hwin package :=
  let next := profiledRawJointLiteralRightBothExactReceiverRecv A strategy hwin
    (package.literalRightSeamInstalled A strategy hwin state.1) state.2.2.1
      own delivered
  let child := package.literalRightSeamBranchChild A strategy hwin state
    next.1
  (⟨state.1, next.1⟩, ⟨state.1, state.2.1, next.2,
    package.literalRightSeamStageOfChild A strategy hwin .first child⟩)

/-- Restarting changes only the retained stage row; the emitted physical and
semantic receiver output is definitionally the legacy branch output. -/
@[simp] theorem literalRightSeamBranchRestartedReceiverRecv_output
    (package : Package A strategy hwin (initial := initial))
    (state :
      ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A
        strategy hwin package)
    (own : In₁) (delivered : In₂) :
    (package.literalRightSeamBranchRestartedReceiverRecv A strategy hwin state
      own delivered).1 =
      (package.literalRightSeamBranchStagedReceiverRecv A strategy hwin state
        own delivered).1 :=
  rfl

@[simp] theorem literalRightSeamBranchRestartedReceiverRecv_key
    (package : Package A strategy hwin (initial := initial))
    (state :
      ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A
        strategy hwin package)
    (own : In₁) (delivered : In₂) :
    (package.literalRightSeamBranchRestartedReceiverRecv A strategy hwin state
      own delivered).2.1 = state.1 :=
  rfl

@[simp] theorem literalRightSeamBranchRestartedReceiverRecv_sourceRow
    (package : Package A strategy hwin (initial := initial))
    (state :
      ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A
        strategy hwin package)
    (own : In₁) (delivered : In₂) :
    (package.literalRightSeamBranchRestartedReceiverRecv A strategy hwin state
      own delivered).2.2.1 = state.2.1 :=
  rfl

theorem literalRightSeamBranchRestartedReceiverRecv_stage
    (package : Package A strategy hwin (initial := initial))
    (state :
      ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A
        strategy hwin package)
    (own : In₁) (delivered : In₂) :
    let result :=
      package.literalRightSeamBranchRestartedReceiverRecv A strategy hwin
        state own delivered
    result.2.2.2.2 =
      package.literalRightSeamStageOfChild A strategy hwin .first
        (package.literalRightSeamBranchChild A strategy hwin state
          result.1.2) :=
  rfl

/-- Any stored restarted stage carries the fresh entry row, independently of
the source row retained by the receiver. -/
theorem literalRightSeamBranchRestartedReceiverRecv_stage_row
    (package : Package A strategy hwin (initial := initial))
    (state :
      ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A
        strategy hwin package)
    (own : In₁) (delivered : In₂)
    (stage : ProfiledRawJointGuardedCommonLiteralRightSeamStage A strategy
      hwin package)
    (hstage :
      (package.literalRightSeamBranchRestartedReceiverRecv A strategy hwin
        state own delivered).2.2.2.2 = some stage) :
    stage.row = .first := by
  rw [package.literalRightSeamBranchRestartedReceiverRecv_stage A strategy
    hwin] at hstage
  exact package.literalRightSeamStageOfChild_row A strategy hwin .first _ _
    hstage

/-- Table reachability gives a live restarted stage just as it gives a live
legacy same-row stage; retagging changes only the stored entry row. -/
theorem
    exists_literalRightSeamBranchRestartedReceiverRecv_stage_of_tableReachable
    (package : Package A strategy hwin (initial := initial))
    (state :
      ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A
        strategy hwin package)
    (own : In₁) (delivered : In₂)
    (hreach : package.LiteralRightSeamReceiverTableLocallyReachable A strategy
      hwin state) :
    ∃ stage : ProfiledRawJointGuardedCommonLiteralRightSeamStage A strategy
        hwin package,
      (package.literalRightSeamBranchRestartedReceiverRecv A strategy hwin
        state own delivered).2.2.2.2 = some stage := by
  obtain ⟨stage, hstage⟩ :=
    package.exists_literalRightSeamBranchStagedReceiverRecv_stage_of_tableReachable
      A strategy hwin state own delivered hreach
  refine ⟨package.literalRightSeamStageRetag A strategy hwin .first stage,
    ?_⟩
  rw [package.literalRightSeamBranchRestartedReceiverRecv_stage A strategy
    hwin]
  rw [package.literalRightSeamStageOfChild_retag A strategy hwin state.2.1
    .first]
  have hmapped := congrArg
    (Option.map
      (package.literalRightSeamStageRetag A strategy hwin .first)) hstage
  simpa [literalRightSeamBranchRestartedReceiverRecv,
    literalRightSeamBranchStagedReceiverRecv] using hmapped

theorem literalRightSeamBranchRestartedReceiverRecv_stage_eq_exact_false
    (package : Package A strategy hwin (initial := initial))
    (state :
      ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A
        strategy hwin package)
    (own : In₁) (delivered : In₂)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (hanchor : state.2.2.1.1 = false)
    (hcode :
      (package.literalRightSeamBranchRestartedReceiverRecv A strategy hwin
        state own delivered).1.2.1.target state.2.1 =
        (package.literalRightSeamTaggedTarget A strategy hwin state.1
          state.2.1 past input).2.1) :
    (package.literalRightSeamBranchRestartedReceiverRecv A strategy hwin state
      own delivered).2.2.2.2 =
      some (package.literalRightSeamExactStageAt A strategy hwin state.1
        state.2.1 .first past input) := by
  rw [package.literalRightSeamBranchRestartedReceiverRecv_stage A strategy
    hwin]
  rw [package.literalRightSeamBranchChild_false A strategy hwin _ _ hanchor]
  rw [hcode]
  rw [package.literalRightSeamTaggedChildOfCode_target A strategy hwin]
  exact package.literalRightSeamStageOfChild_exactAt A strategy hwin state.1
    state.2.1 .first past input

theorem literalRightSeamBranchRestartedReceiverRecv_stage_eq_exact_true
    (package : Package A strategy hwin (initial := initial))
    (state :
      ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A
        strategy hwin package)
    (own : In₁) (delivered : In₂)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (hanchor : state.2.2.1.1 = true)
    (htarget :
      ⟨state.1,
        (package.literalRightSeamBranchRestartedReceiverRecv A strategy hwin
          state own delivered).1.2.2.target state.2.1⟩ =
        package.literalRightSeamTaggedTarget A strategy hwin state.1
          state.2.1 past input) :
    (package.literalRightSeamBranchRestartedReceiverRecv A strategy hwin state
      own delivered).2.2.2.2 =
      some (package.literalRightSeamExactStageAt A strategy hwin state.1
        state.2.1 .first past input) := by
  rw [package.literalRightSeamBranchRestartedReceiverRecv_stage A strategy
    hwin]
  rw [package.literalRightSeamBranchChild_true A strategy hwin _ _ hanchor]
  rw [htarget]
  exact package.literalRightSeamStageOfChild_exactAt A strategy hwin state.1
    state.2.1 .first past input

/-- In particular, the first false-member receive may read the actual common
row `.both` while installing the strict suffix at `.first`. -/
theorem literalRightSeamBranchRestartedReceiverFirst_false_stage
    (package : Package A strategy hwin (initial := initial))
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (sourceRow : PairedEntryRow) (input : In₁ × In₂) :
    (package.literalRightSeamBranchRestartedReceiverRecv A strategy hwin
      (package.literalRightSeamStagedReceiverInitial A strategy hwin key
        sourceRow false)
      input.1 input.2).2.2.2.2 =
      some (package.literalRightSeamExactStageAt A strategy hwin key sourceRow
        .first [] input) := by
  apply package.literalRightSeamBranchRestartedReceiverRecv_stage_eq_exact_false
    A strategy hwin
  · rfl
  · change
      (profiledRawJointLiteralRightBothExactReceiverRecv A strategy hwin
        (package.literalRightSeamInstalled A strategy hwin key)
        (profiledRawJointLiteralRightBothExactReceiverInitial A strategy hwin
          (package.literalRightSeamInstalled A strategy hwin key) false)
        input.1 input.2).1.1.target sourceRow =
        (profiledRawJointGuardedFirstLeftTarget A strategy
          ((package.literalRightSeamInstalled A strategy hwin key).world
            |>.oneSidedState A .left)
          (profiledRawJointHybridExactLeftRootPredicate A
            (package.literalRightSeamInstalled A strategy hwin key))
          (profiledRawJointHybridExactLeftPolicy A hwin
            (package.literalRightSeamInstalled A strategy hwin key))
          sourceRow [] input).1
    exact profiledRawJointLiteralRightBothExactReceiverFirst_false_target_code
      A strategy hwin (package.literalRightSeamInstalled A strategy hwin key)
        sourceRow input

/-! ## Left seam -/

/-- Mirror restarted receive: select at the retained source row, enter the
new strict block at `.first`. -/
noncomputable def literalLeftSeamBranchRestartedReceiverRecv
    (package : Package A strategy hwin (initial := initial))
    (state :
      ProfiledRawJointGuardedCommonLiteralLeftSeamStagedReceiverState A
        strategy hwin package)
    (own : In₂) (delivered : In₁) :
    ProfiledRawJointGuardedCommonLiteralLeftSeamFrontReceiverOutput A strategy
        hwin package ×
      ProfiledRawJointGuardedCommonLiteralLeftSeamStagedReceiverState A
        strategy hwin package :=
  let next := profiledRawJointLiteralLeftBothExactReceiverRecv A strategy hwin
    (package.literalLeftSeamInstalled A strategy hwin state.1) state.2.2.1 own
      delivered
  let child := package.literalLeftSeamBranchChild A strategy hwin state next.1
  (⟨state.1, next.1⟩, ⟨state.1, state.2.1, next.2,
    package.literalLeftSeamStageOfChild A strategy hwin .first child⟩)

/-- Mirror output coincidence: only the stored fresh entry row differs. -/
@[simp] theorem literalLeftSeamBranchRestartedReceiverRecv_output
    (package : Package A strategy hwin (initial := initial))
    (state :
      ProfiledRawJointGuardedCommonLiteralLeftSeamStagedReceiverState A
        strategy hwin package)
    (own : In₂) (delivered : In₁) :
    (package.literalLeftSeamBranchRestartedReceiverRecv A strategy hwin state
      own delivered).1 =
      (package.literalLeftSeamBranchStagedReceiverRecv A strategy hwin state
        own delivered).1 :=
  rfl

@[simp] theorem literalLeftSeamBranchRestartedReceiverRecv_key
    (package : Package A strategy hwin (initial := initial))
    (state :
      ProfiledRawJointGuardedCommonLiteralLeftSeamStagedReceiverState A
        strategy hwin package)
    (own : In₂) (delivered : In₁) :
    (package.literalLeftSeamBranchRestartedReceiverRecv A strategy hwin state
      own delivered).2.1 = state.1 :=
  rfl

@[simp] theorem literalLeftSeamBranchRestartedReceiverRecv_sourceRow
    (package : Package A strategy hwin (initial := initial))
    (state :
      ProfiledRawJointGuardedCommonLiteralLeftSeamStagedReceiverState A
        strategy hwin package)
    (own : In₂) (delivered : In₁) :
    (package.literalLeftSeamBranchRestartedReceiverRecv A strategy hwin state
      own delivered).2.2.1 = state.2.1 :=
  rfl

theorem literalLeftSeamBranchRestartedReceiverRecv_stage
    (package : Package A strategy hwin (initial := initial))
    (state :
      ProfiledRawJointGuardedCommonLiteralLeftSeamStagedReceiverState A
        strategy hwin package)
    (own : In₂) (delivered : In₁) :
    let result :=
      package.literalLeftSeamBranchRestartedReceiverRecv A strategy hwin state
        own delivered
    result.2.2.2.2 =
      package.literalLeftSeamStageOfChild A strategy hwin .first
        (package.literalLeftSeamBranchChild A strategy hwin state
          result.1.2) :=
  rfl

theorem literalLeftSeamBranchRestartedReceiverRecv_stage_row
    (package : Package A strategy hwin (initial := initial))
    (state :
      ProfiledRawJointGuardedCommonLiteralLeftSeamStagedReceiverState A
        strategy hwin package)
    (own : In₂) (delivered : In₁)
    (stage : ProfiledRawJointGuardedCommonLiteralLeftSeamStage A strategy hwin
      package)
    (hstage :
      (package.literalLeftSeamBranchRestartedReceiverRecv A strategy hwin
        state own delivered).2.2.2.2 = some stage) :
    stage.row = .first := by
  rw [package.literalLeftSeamBranchRestartedReceiverRecv_stage A strategy
    hwin] at hstage
  exact package.literalLeftSeamStageOfChild_row A strategy hwin .first _ _
    hstage

theorem literalLeftSeamBranchRestartedReceiverRecv_stage_eq_exact_false
    (package : Package A strategy hwin (initial := initial))
    (state :
      ProfiledRawJointGuardedCommonLiteralLeftSeamStagedReceiverState A
        strategy hwin package)
    (own : In₂) (delivered : In₁)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (hanchor : state.2.2.1.1 = false)
    (hcode :
      (package.literalLeftSeamBranchRestartedReceiverRecv A strategy hwin
        state own delivered).1.2.1.target state.2.1 =
        (package.literalLeftSeamTaggedTarget A strategy hwin state.1
          state.2.1 past input).2.1) :
    (package.literalLeftSeamBranchRestartedReceiverRecv A strategy hwin state
      own delivered).2.2.2.2 =
      some (package.literalLeftSeamExactStageAt A strategy hwin state.1
        state.2.1 .first past input) := by
  rw [package.literalLeftSeamBranchRestartedReceiverRecv_stage A strategy
    hwin]
  rw [package.literalLeftSeamBranchChild_false A strategy hwin _ _ hanchor]
  rw [hcode]
  rw [package.literalLeftSeamTaggedChildOfCode_target A strategy hwin]
  exact package.literalLeftSeamStageOfChild_exactAt A strategy hwin state.1
    state.2.1 .first past input

theorem literalLeftSeamBranchRestartedReceiverRecv_stage_eq_exact_true
    (package : Package A strategy hwin (initial := initial))
    (state :
      ProfiledRawJointGuardedCommonLiteralLeftSeamStagedReceiverState A
        strategy hwin package)
    (own : In₂) (delivered : In₁)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (hanchor : state.2.2.1.1 = true)
    (htarget :
      ⟨state.1,
        (package.literalLeftSeamBranchRestartedReceiverRecv A strategy hwin
          state own delivered).1.2.2.target state.2.1⟩ =
        package.literalLeftSeamTaggedTarget A strategy hwin state.1
          state.2.1 past input) :
    (package.literalLeftSeamBranchRestartedReceiverRecv A strategy hwin state
      own delivered).2.2.2.2 =
      some (package.literalLeftSeamExactStageAt A strategy hwin state.1
        state.2.1 .first past input) := by
  rw [package.literalLeftSeamBranchRestartedReceiverRecv_stage A strategy
    hwin]
  rw [package.literalLeftSeamBranchChild_true A strategy hwin _ _ hanchor]
  rw [htarget]
  exact package.literalLeftSeamStageOfChild_exactAt A strategy hwin state.1
    state.2.1 .first past input

theorem literalLeftSeamBranchRestartedReceiverFirst_false_stage
    (package : Package A strategy hwin (initial := initial))
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package)
    (sourceRow : PairedEntryRow) (input : In₂ × In₁) :
    (package.literalLeftSeamBranchRestartedReceiverRecv A strategy hwin
      (package.literalLeftSeamStagedReceiverInitial A strategy hwin key
        sourceRow false)
      input.1 input.2).2.2.2.2 =
      some (package.literalLeftSeamExactStageAt A strategy hwin key sourceRow
        .first [] input) := by
  apply package.literalLeftSeamBranchRestartedReceiverRecv_stage_eq_exact_false
    A strategy hwin
  · rfl
  · change
      (profiledRawJointLiteralLeftBothExactReceiverRecv A strategy hwin
        (package.literalLeftSeamInstalled A strategy hwin key)
        (profiledRawJointLiteralLeftBothExactReceiverInitial A strategy hwin
          (package.literalLeftSeamInstalled A strategy hwin key) false)
        input.1 input.2).1.1.target sourceRow =
        (profiledRawJointGuardedFirstRightTarget A strategy
          ((package.literalLeftSeamInstalled A strategy hwin key).world
            |>.oneSidedState A .right)
          (profiledRawJointHybridExactRightRootPredicate A
            (package.literalLeftSeamInstalled A strategy hwin key))
          (profiledRawJointHybridExactRightPolicy A hwin
            (package.literalLeftSeamInstalled A strategy hwin key))
          sourceRow [] input).1
    exact profiledRawJointLiteralLeftBothExactReceiverFirst_false_target_code
      A strategy hwin (package.literalLeftSeamInstalled A strategy hwin key)
        sourceRow input

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
