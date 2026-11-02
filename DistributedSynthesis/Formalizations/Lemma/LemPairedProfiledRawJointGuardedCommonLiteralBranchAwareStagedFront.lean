/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralHeterogeneousSeamTaggedStagedFront
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralExactMirrorTaggedStagedFront
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointCrossReceiverPhysicalProjection

/-!
# Branch-aware retained stages at both literal seams

The heterogeneous receiver output contains a false and a true semantic
coordinate.  Only the coordinate selected by the receiver's *internal*
anchor is live.  In particular, a retained receiver may still have internal
anchor `true` after an outer delayed-member control has been re-encapsulated
with member `false`.

This module makes the selection local and explicit.  The true coordinate
already contains an exact dependent literal child.  The false coordinate
contains only its finite incidence code, so we totalize the finite inverse
from codes to literal children and prove that it recovers every exact tagged
target.  No executable function receives a graph, orientation, hierarchy
side, leader bit, history, or semantic view.
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

/-! ## Total finite inverses of the active false code -/

/-- At a fixed right-seam key, choose a literal child having the requested
incidence code when one exists, and otherwise choose the inhabited fallback.
The fallback only totalizes malformed controls. -/
noncomputable def literalRightSeamTaggedChildOfCode
    (package : Package A strategy hwin (initial := initial))
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (code : ProfiledRawJointIncidenceCode A (I := Unit)) :
    ProfiledRawJointGuardedCommonLiteralRightSeamTaggedChildCode A strategy
      hwin package := by
  classical
  by_cases hex : ∃ child : ProfiledRawJointOneSidedLiteralChildCode A
      strategy
        (ProfiledRawJointGuardedCommonLiteralRightSeamSelectedSource A
          strategy hwin package key), child.1 = code
  · exact ⟨key, Classical.choose hex⟩
  · exact ⟨key, default⟩

/-- The total inverse is exact on every semantic tagged target. -/
theorem literalRightSeamTaggedChildOfCode_target
    (package : Package A strategy hwin (initial := initial))
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    package.literalRightSeamTaggedChildOfCode A strategy hwin key
        (package.literalRightSeamTaggedTarget A strategy hwin key row past
          input).2.1 =
      package.literalRightSeamTaggedTarget A strategy hwin key row past
        input := by
  classical
  let target := package.literalRightSeamTaggedTarget A strategy hwin key row
    past input
  have hex : ∃ child : ProfiledRawJointOneSidedLiteralChildCode A strategy
      (ProfiledRawJointGuardedCommonLiteralRightSeamSelectedSource A strategy
        hwin package key), child.1 = target.2.1 :=
    ⟨target.2, rfl⟩
  rw [literalRightSeamTaggedChildOfCode]
  split
  · rename_i hchosen
    apply Sigma.ext
    · rfl
    · exact heq_of_eq (Subtype.ext (Classical.choose_spec hchosen))
  · rename_i hnot
    exfalso
    exact hnot hex

/-- Mirror total inverse for the active false code at the left seam. -/
noncomputable def literalLeftSeamTaggedChildOfCode
    (package : Package A strategy hwin (initial := initial))
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package)
    (code : ProfiledRawJointIncidenceCode A (I := Unit)) :
    ProfiledRawJointGuardedCommonLiteralLeftSeamTaggedChildCode A strategy
      hwin package := by
  classical
  by_cases hex : ∃ child : ProfiledRawJointOneSidedLiteralChildCode A
      strategy
        (ProfiledRawJointGuardedCommonLiteralLeftSeamSelectedSource A strategy
          hwin package key), child.1 = code
  · exact ⟨key, Classical.choose hex⟩
  · exact ⟨key, default⟩

/-- The mirror inverse is exact on every semantic tagged target. -/
theorem literalLeftSeamTaggedChildOfCode_target
    (package : Package A strategy hwin (initial := initial))
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    package.literalLeftSeamTaggedChildOfCode A strategy hwin key
        (package.literalLeftSeamTaggedTarget A strategy hwin key row past
          input).2.1 =
      package.literalLeftSeamTaggedTarget A strategy hwin key row past
        input := by
  classical
  let target := package.literalLeftSeamTaggedTarget A strategy hwin key row
    past input
  have hex : ∃ child : ProfiledRawJointOneSidedLiteralChildCode A strategy
      (ProfiledRawJointGuardedCommonLiteralLeftSeamSelectedSource A strategy
        hwin package key), child.1 = target.2.1 :=
    ⟨target.2, rfl⟩
  rw [literalLeftSeamTaggedChildOfCode]
  split
  · rename_i hchosen
    apply Sigma.ext
    · rfl
    · exact heq_of_eq (Subtype.ext (Classical.choose_spec hchosen))
  · rename_i hnot
    exfalso
    exact hnot hex

/-! ## Branch-aware right receiver -/

/-- Read the current right-seam child from the internally active coordinate.
The anchor is stored in the finite receiver state itself. -/
noncomputable def literalRightSeamBranchChild
    (package : Package A strategy hwin (initial := initial))
    (state :
      ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A
        strategy hwin package)
    (output :
      ProfiledRawJointLiteralRightBothExactProductReceiverOutput A strategy
        hwin (package.literalRightSeamInstalled A strategy hwin state.1)) :
    ProfiledRawJointGuardedCommonLiteralRightSeamTaggedChildCode A strategy
      hwin package :=
  if state.2.2.1.1 then
    ⟨state.1, output.2.target state.2.1⟩
  else
    package.literalRightSeamTaggedChildOfCode A strategy hwin state.1
      (output.1.target state.2.1)

@[simp] theorem literalRightSeamBranchChild_false
    (package : Package A strategy hwin (initial := initial))
    (state :
      ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A
        strategy hwin package)
    (output :
      ProfiledRawJointLiteralRightBothExactProductReceiverOutput A strategy
        hwin (package.literalRightSeamInstalled A strategy hwin state.1))
    (hanchor : state.2.2.1.1 = false) :
    package.literalRightSeamBranchChild A strategy hwin state output =
      package.literalRightSeamTaggedChildOfCode A strategy hwin state.1
        (output.1.target state.2.1) := by
  simp [literalRightSeamBranchChild, hanchor]

@[simp] theorem literalRightSeamBranchChild_true
    (package : Package A strategy hwin (initial := initial))
    (state :
      ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A
        strategy hwin package)
    (output :
      ProfiledRawJointLiteralRightBothExactProductReceiverOutput A strategy
        hwin (package.literalRightSeamInstalled A strategy hwin state.1))
    (hanchor : state.2.2.1.1 = true) :
    package.literalRightSeamBranchChild A strategy hwin state output =
      ⟨state.1, output.2.target state.2.1⟩ := by
  simp [literalRightSeamBranchChild, hanchor]

/-- Replace the retained stage from the internally active coordinate while
leaving the heterogeneous table transition itself unchanged. -/
noncomputable def literalRightSeamBranchStagedReceiverRecv
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
    package.literalRightSeamStageOfChild A strategy hwin state.2.1 child⟩)

@[simp] theorem literalRightSeamBranchStagedReceiverRecv_key
    (package : Package A strategy hwin (initial := initial))
    (state :
      ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A
        strategy hwin package)
    (own : In₁) (delivered : In₂) :
    (package.literalRightSeamBranchStagedReceiverRecv A strategy hwin state
      own delivered).2.1 = state.1 :=
  rfl

@[simp] theorem literalRightSeamBranchStagedReceiverRecv_row
    (package : Package A strategy hwin (initial := initial))
    (state :
      ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A
        strategy hwin package)
    (own : In₁) (delivered : In₂) :
    (package.literalRightSeamBranchStagedReceiverRecv A strategy hwin state
      own delivered).2.2.1 = state.2.1 :=
  rfl

theorem literalRightSeamBranchStagedReceiverRecv_stage
    (package : Package A strategy hwin (initial := initial))
    (state :
      ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A
        strategy hwin package)
    (own : In₁) (delivered : In₂) :
    let result := package.literalRightSeamBranchStagedReceiverRecv A strategy
      hwin state own delivered
    result.2.2.2.2 =
      package.literalRightSeamStageOfChild A strategy hwin state.2.1
        (package.literalRightSeamBranchChild A strategy hwin state
          result.1.2) :=
  rfl

/-- On an internally false right receiver, equality of the active incidence
code with one semantic target is sufficient for an exact live stage. -/
theorem literalRightSeamBranchStagedReceiverRecv_stage_eq_exact_false
    (package : Package A strategy hwin (initial := initial))
    (state :
      ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A
        strategy hwin package)
    (own : In₁) (delivered : In₂)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (hanchor : state.2.2.1.1 = false)
    (hcode :
      (package.literalRightSeamBranchStagedReceiverRecv A strategy hwin state
        own delivered).1.2.1.target state.2.1 =
        (package.literalRightSeamTaggedTarget A strategy hwin state.1
          state.2.1 past input).2.1) :
    (package.literalRightSeamBranchStagedReceiverRecv A strategy hwin state
      own delivered).2.2.2.2 =
      some (package.literalRightSeamExactStage A strategy hwin state.1
        state.2.1 past input) := by
  rw [package.literalRightSeamBranchStagedReceiverRecv_stage A strategy hwin]
  rw [package.literalRightSeamBranchChild_false A strategy hwin _ _ hanchor]
  rw [hcode]
  rw [package.literalRightSeamTaggedChildOfCode_target A strategy hwin]
  exact package.literalRightSeamStageOfChild_exact A strategy hwin state.1
    state.2.1 past input

/-- The true branch is the original exact dependent-coordinate refresh. -/
theorem literalRightSeamBranchStagedReceiverRecv_stage_eq_exact_true
    (package : Package A strategy hwin (initial := initial))
    (state :
      ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A
        strategy hwin package)
    (own : In₁) (delivered : In₂)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (hanchor : state.2.2.1.1 = true)
    (htarget :
      ⟨state.1,
        (package.literalRightSeamBranchStagedReceiverRecv A strategy hwin
          state own delivered).1.2.2.target state.2.1⟩ =
        package.literalRightSeamTaggedTarget A strategy hwin state.1
          state.2.1 past input) :
    (package.literalRightSeamBranchStagedReceiverRecv A strategy hwin state
      own delivered).2.2.2.2 =
      some (package.literalRightSeamExactStage A strategy hwin state.1
        state.2.1 past input) := by
  rw [package.literalRightSeamBranchStagedReceiverRecv_stage A strategy hwin]
  rw [package.literalRightSeamBranchChild_true A strategy hwin _ _ hanchor]
  rw [htarget]
  exact package.literalRightSeamStageOfChild_exact A strategy hwin state.1
    state.2.1 past input

/-- The very first false-member right receive now installs the exact stage
from its active code, rather than consulting the unconstrained true field. -/
theorem literalRightSeamBranchStagedReceiverFirst_false_stage
    (package : Package A strategy hwin (initial := initial))
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (input : In₁ × In₂) :
    (package.literalRightSeamBranchStagedReceiverRecv A strategy hwin
      (package.literalRightSeamStagedReceiverInitial A strategy hwin key row
        false)
      input.1 input.2).2.2.2.2 =
      some (package.literalRightSeamExactStage A strategy hwin key row []
        input) := by
  apply package.literalRightSeamBranchStagedReceiverRecv_stage_eq_exact_false
    A strategy hwin
  · rfl
  · change
      (profiledRawJointLiteralRightBothExactReceiverRecv A strategy hwin
        (package.literalRightSeamInstalled A strategy hwin key)
        (profiledRawJointLiteralRightBothExactReceiverInitial A strategy hwin
          (package.literalRightSeamInstalled A strategy hwin key) false)
        input.1 input.2).1.1.target row =
        (profiledRawJointGuardedFirstLeftTarget A strategy
          ((package.literalRightSeamInstalled A strategy hwin key).world
            |>.oneSidedState A .left)
          (profiledRawJointHybridExactLeftRootPredicate A
            (package.literalRightSeamInstalled A strategy hwin key))
          (profiledRawJointHybridExactLeftPolicy A hwin
            (package.literalRightSeamInstalled A strategy hwin key))
          row [] input).1
    exact profiledRawJointLiteralRightBothExactReceiverFirst_false_target_code
      A strategy hwin (package.literalRightSeamInstalled A strategy hwin key)
        row input

/-- The true first receive remains the original exact dependent refresh. -/
theorem literalRightSeamBranchStagedReceiverFirst_true_stage
    (package : Package A strategy hwin (initial := initial))
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (input : In₁ × In₂) :
    (package.literalRightSeamBranchStagedReceiverRecv A strategy hwin
      (package.literalRightSeamStagedReceiverInitial A strategy hwin key row
        true)
      input.1 input.2).2.2.2.2 =
      some (package.literalRightSeamExactStage A strategy hwin key row []
        input) := by
  apply package.literalRightSeamBranchStagedReceiverRecv_stage_eq_exact_true
    A strategy hwin
  · rfl
  · have htarget := package.literalRightSeamFrontTrueFirst_target A strategy
      hwin key row input
    simpa [literalRightSeamBranchStagedReceiverRecv,
      literalRightSeamStagedReceiverInitial,
      literalRightSeamFrontFirstRound,
      literalRightSeamFrontReceiverRecv,
      literalRightSeamFrontReceiverInitial,
      literalRightSeamFrontSenderNoRecv,
      literalRightSeamFrontSenderInitial] using htarget

/-- Select process one's physical output using the receiver's internal live
anchor, independently of any outer delayed-member wrapper. -/
noncomputable def literalRightSeamInternalPhysicalOutput
    (package : Package A strategy hwin (initial := initial))
    (state :
      ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A
        strategy hwin package)
    (output :
      ProfiledRawJointGuardedCommonLiteralRightSeamFrontReceiverOutput A
        strategy hwin package) : Out₁ :=
  if state.2.2.1.1 then
    profiledRawJointTargetLeftReceiverBothPhysicalOutput output.2.2
  else
    profiledRawJointTargetLeftReceiverBothPhysicalOutput output.2.1

@[simp] theorem literalRightSeamInternalPhysicalOutput_false
    (package : Package A strategy hwin (initial := initial))
    (state :
      ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A
        strategy hwin package)
    (output :
      ProfiledRawJointGuardedCommonLiteralRightSeamFrontReceiverOutput A
        strategy hwin package)
    (hanchor : state.2.2.1.1 = false) :
    package.literalRightSeamInternalPhysicalOutput A strategy hwin state
        output =
      profiledRawJointTargetLeftReceiverBothPhysicalOutput output.2.1 := by
  simp [literalRightSeamInternalPhysicalOutput, hanchor]

@[simp] theorem literalRightSeamInternalPhysicalOutput_true
    (package : Package A strategy hwin (initial := initial))
    (state :
      ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A
        strategy hwin package)
    (output :
      ProfiledRawJointGuardedCommonLiteralRightSeamFrontReceiverOutput A
        strategy hwin package)
    (hanchor : state.2.2.1.1 = true) :
    package.literalRightSeamInternalPhysicalOutput A strategy hwin state
        output =
      profiledRawJointTargetLeftReceiverBothPhysicalOutput output.2.2 := by
  simp [literalRightSeamInternalPhysicalOutput, hanchor]

/-! ## Branch-aware mirror receiver -/

noncomputable def literalLeftSeamBranchChild
    (package : Package A strategy hwin (initial := initial))
    (state :
      ProfiledRawJointGuardedCommonLiteralLeftSeamStagedReceiverState A
        strategy hwin package)
    (output :
      ProfiledRawJointLiteralLeftBothExactProductReceiverOutput A strategy
        hwin (package.literalLeftSeamInstalled A strategy hwin state.1)) :
    ProfiledRawJointGuardedCommonLiteralLeftSeamTaggedChildCode A strategy
      hwin package :=
  if state.2.2.1.1 then
    ⟨state.1, output.2.target state.2.1⟩
  else
    package.literalLeftSeamTaggedChildOfCode A strategy hwin state.1
      (output.1.target state.2.1)

@[simp] theorem literalLeftSeamBranchChild_false
    (package : Package A strategy hwin (initial := initial))
    (state :
      ProfiledRawJointGuardedCommonLiteralLeftSeamStagedReceiverState A
        strategy hwin package)
    (output :
      ProfiledRawJointLiteralLeftBothExactProductReceiverOutput A strategy
        hwin (package.literalLeftSeamInstalled A strategy hwin state.1))
    (hanchor : state.2.2.1.1 = false) :
    package.literalLeftSeamBranchChild A strategy hwin state output =
      package.literalLeftSeamTaggedChildOfCode A strategy hwin state.1
        (output.1.target state.2.1) := by
  simp [literalLeftSeamBranchChild, hanchor]

@[simp] theorem literalLeftSeamBranchChild_true
    (package : Package A strategy hwin (initial := initial))
    (state :
      ProfiledRawJointGuardedCommonLiteralLeftSeamStagedReceiverState A
        strategy hwin package)
    (output :
      ProfiledRawJointLiteralLeftBothExactProductReceiverOutput A strategy
        hwin (package.literalLeftSeamInstalled A strategy hwin state.1))
    (hanchor : state.2.2.1.1 = true) :
    package.literalLeftSeamBranchChild A strategy hwin state output =
      ⟨state.1, output.2.target state.2.1⟩ := by
  simp [literalLeftSeamBranchChild, hanchor]

noncomputable def literalLeftSeamBranchStagedReceiverRecv
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
    package.literalLeftSeamStageOfChild A strategy hwin state.2.1 child⟩)

@[simp] theorem literalLeftSeamBranchStagedReceiverRecv_key
    (package : Package A strategy hwin (initial := initial))
    (state :
      ProfiledRawJointGuardedCommonLiteralLeftSeamStagedReceiverState A
        strategy hwin package)
    (own : In₂) (delivered : In₁) :
    (package.literalLeftSeamBranchStagedReceiverRecv A strategy hwin state own
      delivered).2.1 = state.1 :=
  rfl

@[simp] theorem literalLeftSeamBranchStagedReceiverRecv_row
    (package : Package A strategy hwin (initial := initial))
    (state :
      ProfiledRawJointGuardedCommonLiteralLeftSeamStagedReceiverState A
        strategy hwin package)
    (own : In₂) (delivered : In₁) :
    (package.literalLeftSeamBranchStagedReceiverRecv A strategy hwin state own
      delivered).2.2.1 = state.2.1 :=
  rfl

theorem literalLeftSeamBranchStagedReceiverRecv_stage
    (package : Package A strategy hwin (initial := initial))
    (state :
      ProfiledRawJointGuardedCommonLiteralLeftSeamStagedReceiverState A
        strategy hwin package)
    (own : In₂) (delivered : In₁) :
    let result := package.literalLeftSeamBranchStagedReceiverRecv A strategy
      hwin state own delivered
    result.2.2.2.2 =
      package.literalLeftSeamStageOfChild A strategy hwin state.2.1
        (package.literalLeftSeamBranchChild A strategy hwin state
          result.1.2) :=
  rfl

theorem literalLeftSeamBranchStagedReceiverRecv_stage_eq_exact_false
    (package : Package A strategy hwin (initial := initial))
    (state :
      ProfiledRawJointGuardedCommonLiteralLeftSeamStagedReceiverState A
        strategy hwin package)
    (own : In₂) (delivered : In₁)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (hanchor : state.2.2.1.1 = false)
    (hcode :
      (package.literalLeftSeamBranchStagedReceiverRecv A strategy hwin state
        own delivered).1.2.1.target state.2.1 =
        (package.literalLeftSeamTaggedTarget A strategy hwin state.1
          state.2.1 past input).2.1) :
    (package.literalLeftSeamBranchStagedReceiverRecv A strategy hwin state own
      delivered).2.2.2.2 =
      some (package.literalLeftSeamExactStage A strategy hwin state.1
        state.2.1 past input) := by
  rw [package.literalLeftSeamBranchStagedReceiverRecv_stage A strategy hwin]
  rw [package.literalLeftSeamBranchChild_false A strategy hwin _ _ hanchor]
  rw [hcode]
  rw [package.literalLeftSeamTaggedChildOfCode_target A strategy hwin]
  exact package.literalLeftSeamStageOfChild_exact A strategy hwin state.1
    state.2.1 past input

theorem literalLeftSeamBranchStagedReceiverRecv_stage_eq_exact_true
    (package : Package A strategy hwin (initial := initial))
    (state :
      ProfiledRawJointGuardedCommonLiteralLeftSeamStagedReceiverState A
        strategy hwin package)
    (own : In₂) (delivered : In₁)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (hanchor : state.2.2.1.1 = true)
    (htarget :
      ⟨state.1,
        (package.literalLeftSeamBranchStagedReceiverRecv A strategy hwin state
          own delivered).1.2.2.target state.2.1⟩ =
        package.literalLeftSeamTaggedTarget A strategy hwin state.1
          state.2.1 past input) :
    (package.literalLeftSeamBranchStagedReceiverRecv A strategy hwin state own
      delivered).2.2.2.2 =
      some (package.literalLeftSeamExactStage A strategy hwin state.1
        state.2.1 past input) := by
  rw [package.literalLeftSeamBranchStagedReceiverRecv_stage A strategy hwin]
  rw [package.literalLeftSeamBranchChild_true A strategy hwin _ _ hanchor]
  rw [htarget]
  exact package.literalLeftSeamStageOfChild_exact A strategy hwin state.1
    state.2.1 past input

theorem literalLeftSeamBranchStagedReceiverFirst_false_stage
    (package : Package A strategy hwin (initial := initial))
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (input : In₂ × In₁) :
    (package.literalLeftSeamBranchStagedReceiverRecv A strategy hwin
      (package.literalLeftSeamStagedReceiverInitial A strategy hwin key row
        false)
      input.1 input.2).2.2.2.2 =
      some (package.literalLeftSeamExactStage A strategy hwin key row []
        input) := by
  apply package.literalLeftSeamBranchStagedReceiverRecv_stage_eq_exact_false
    A strategy hwin
  · rfl
  · change
      (profiledRawJointLiteralLeftBothExactReceiverRecv A strategy hwin
        (package.literalLeftSeamInstalled A strategy hwin key)
        (profiledRawJointLiteralLeftBothExactReceiverInitial A strategy hwin
          (package.literalLeftSeamInstalled A strategy hwin key) false)
        input.1 input.2).1.1.target row =
        (profiledRawJointGuardedFirstRightTarget A strategy
          ((package.literalLeftSeamInstalled A strategy hwin key).world
            |>.oneSidedState A .right)
          (profiledRawJointHybridExactRightRootPredicate A
            (package.literalLeftSeamInstalled A strategy hwin key))
          (profiledRawJointHybridExactRightPolicy A hwin
            (package.literalLeftSeamInstalled A strategy hwin key))
          row [] input).1
    exact profiledRawJointLiteralLeftBothExactReceiverFirst_false_target_code
      A strategy hwin (package.literalLeftSeamInstalled A strategy hwin key)
        row input

theorem literalLeftSeamBranchStagedReceiverFirst_true_stage
    (package : Package A strategy hwin (initial := initial))
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (input : In₂ × In₁) :
    (package.literalLeftSeamBranchStagedReceiverRecv A strategy hwin
      (package.literalLeftSeamStagedReceiverInitial A strategy hwin key row
        true)
      input.1 input.2).2.2.2.2 =
      some (package.literalLeftSeamExactStage A strategy hwin key row []
        input) := by
  apply package.literalLeftSeamBranchStagedReceiverRecv_stage_eq_exact_true
    A strategy hwin
  · rfl
  · have htarget := package.literalLeftSeamFrontTrueFirst_target A strategy
      hwin key row input
    simpa [literalLeftSeamBranchStagedReceiverRecv,
      literalLeftSeamStagedReceiverInitial,
      literalLeftSeamFrontFirstRound,
      literalLeftSeamFrontReceiverRecv,
      literalLeftSeamFrontReceiverInitial,
      literalLeftSeamFrontSenderNoRecv,
      literalLeftSeamFrontSenderInitial] using htarget

/-- Mirror internal-anchor physical output selector for process two. -/
noncomputable def literalLeftSeamInternalPhysicalOutput
    (package : Package A strategy hwin (initial := initial))
    (state :
      ProfiledRawJointGuardedCommonLiteralLeftSeamStagedReceiverState A
        strategy hwin package)
    (output :
      ProfiledRawJointGuardedCommonLiteralLeftSeamFrontReceiverOutput A
        strategy hwin package) : Out₂ :=
  if state.2.2.1.1 then
    profiledRawJointTargetRightReceiverBothPhysicalOutput output.2.2
  else
    profiledRawJointTargetRightReceiverBothPhysicalOutput output.2.1

@[simp] theorem literalLeftSeamInternalPhysicalOutput_false
    (package : Package A strategy hwin (initial := initial))
    (state :
      ProfiledRawJointGuardedCommonLiteralLeftSeamStagedReceiverState A
        strategy hwin package)
    (output :
      ProfiledRawJointGuardedCommonLiteralLeftSeamFrontReceiverOutput A
        strategy hwin package)
    (hanchor : state.2.2.1.1 = false) :
    package.literalLeftSeamInternalPhysicalOutput A strategy hwin state
        output =
      profiledRawJointTargetRightReceiverBothPhysicalOutput output.2.1 := by
  simp [literalLeftSeamInternalPhysicalOutput, hanchor]

@[simp] theorem literalLeftSeamInternalPhysicalOutput_true
    (package : Package A strategy hwin (initial := initial))
    (state :
      ProfiledRawJointGuardedCommonLiteralLeftSeamStagedReceiverState A
        strategy hwin package)
    (output :
      ProfiledRawJointGuardedCommonLiteralLeftSeamFrontReceiverOutput A
        strategy hwin package)
    (hanchor : state.2.2.1.1 = true) :
    package.literalLeftSeamInternalPhysicalOutput A strategy hwin state
        output =
      profiledRawJointTargetRightReceiverBothPhysicalOutput output.2.2 := by
  simp [literalLeftSeamInternalPhysicalOutput, hanchor]

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
