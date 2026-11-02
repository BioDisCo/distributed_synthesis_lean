/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshReceiveOneHandler
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralHeterogeneousSeamTaggedStagedFront

/-!
# Exact reduction of the blind right-activation output bridge

At a left-to-right reversal, process one cannot distinguish the strict-left
predecessor from a simultaneous predecessor.  Its combined pending control
therefore keeps executing the shared left-seam table.  The proof-side staged
right continuation, on the other hand, starts the independently selected
ordinary controller below the exact staged child.

This file unfolds both sides at an exact stage.  It proves all equalities
which follow from the present constructors and isolates the remaining fact as
one equality of output functions.  In particular, it does not ask for control
state equality and does not expose a graph, orientation, leader bit, history,
or semantic view to an executable transition.
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

private abbrev Key (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin package

private abbrev FreshOne :=
  ProfiledRawJointGuardedCommonDecoratedFreshnessOneState A strategy hwin
    initial

private abbrev RightReceiver (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A strategy
    hwin package

private abbrev OneShared (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralCombinedFreshOneShared A strategy hwin
    package

/-! ## The whole unresolved homogeneous epoch -/

/-- Iterate the actual combined pending transition through a chronological
list of blind process-one inputs.  This is the operational state used for the
whole homogeneous epoch; no recurrent controller is entered between its
letters. -/
noncomputable def literalCombinedFreshRightPendingRun
    (package : Package A strategy hwin initial) (member : Bool) :
    OneShared A strategy hwin package → List In₁ →
      OneShared A strategy hwin package
  | shared, [] => shared
  | shared, input :: rest =>
      literalCombinedFreshRightPendingRun package member
        (package.literalCombinedFreshOnePendingStep A strategy hwin member
          shared input).1 rest

/-- The complete pending state after an arbitrary blind suffix is independent
of the hidden interpretation.  This is stronger than root-output agreement:
the two interpretations keep one literally shared table state throughout the
homogeneous epoch. -/
theorem literalCombinedFreshRightPendingRun_member_eq
    (package : Package A strategy hwin initial)
    (left right : Bool) (shared : OneShared A strategy hwin package)
    (past : List In₁) :
    package.literalCombinedFreshRightPendingRun A strategy hwin left shared
        past =
      package.literalCombinedFreshRightPendingRun A strategy hwin right shared
        past := by
  induction past generalizing shared with
  | nil => rfl
  | cons input rest ih =>
      simp only [literalCombinedFreshRightPendingRun]
      exact ih _

/-- Consequently the next physical output is coherent after every finite
blind suffix, not only at the fresh root. -/
theorem literalCombinedFreshRightPendingRun_output_eq
    (package : Package A strategy hwin initial)
    (left right : Bool) (shared : OneShared A strategy hwin package)
    (past : List In₁) (input : In₁) :
    (package.literalCombinedFreshOnePendingStep A strategy hwin left
      (package.literalCombinedFreshRightPendingRun A strategy hwin left shared
        past) input).2 =
    (package.literalCombinedFreshOnePendingStep A strategy hwin right
      (package.literalCombinedFreshRightPendingRun A strategy hwin right shared
        past) input).2 := by
  rw [package.literalCombinedFreshRightPendingRun_member_eq A strategy hwin
    left right shared past]
  exact
    (package.literalCombinedFreshOnePendingStepLaws A strategy hwin).output_eq
      left right _ input

/-! ## The two root output functions -/

/-- Process one's actual pending output at a freshly installed combined
control.  The member is retained in the statement to make its operational
irrelevance explicit. -/
noncomputable def literalCombinedFreshRightPendingInitialOutput
    (package : Package A strategy hwin initial)
    (fresh : FreshOne A strategy hwin (initial := initial))
    (key : Key A strategy hwin package) (member : Bool) (input : In₁) :
    Out₁ :=
  (package.literalCombinedFreshOnePendingStep A strategy hwin member
    (package.literalCrossCombinedFreshOneSharedAt A strategy hwin fresh key)
    input).2

/-- The pending output is literally the output of the fresh left-seam table
sender. -/
@[simp] theorem literalCombinedFreshRightPendingInitialOutput_eq_table
    (package : Package A strategy hwin initial)
    (fresh : FreshOne A strategy hwin (initial := initial))
    (key : Key A strategy hwin package) (member : Bool) (input : In₁) :
    package.literalCombinedFreshRightPendingInitialOutput A strategy hwin
        fresh key member input =
      (package.literalLeftSeamStagedSenderNoRecv A strategy hwin
        (package.literalLeftSeamStagedSenderInitial A strategy hwin key)
        input).1 :=
  rfl

/-- A staged receiver whose live option is exactly the root-pinned stage at
`(key,row,past,recordInput)`.  The old table receiver component is irrelevant
to reversal activation, so its canonical true root is used. -/
noncomputable def literalRightSeamReceiverAtExactStage
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package) (row : PairedEntryRow)
    (past : List (In₁ × In₂)) (recordInput : In₁ × In₂) :
    RightReceiver A strategy hwin package :=
  let root := package.literalRightSeamStagedReceiverInitial A strategy hwin
    key row true
  ⟨key, row, root.2.2.1,
    some (package.literalRightSeamExactStage A strategy hwin key row past
      recordInput)⟩

@[simp] theorem literalRightSeamReceiverAtExactStage_stage
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package) (row : PairedEntryRow)
    (past : List (In₁ × In₂)) (recordInput : In₁ × In₂) :
    (package.literalRightSeamReceiverAtExactStage A strategy hwin key row past
      recordInput).2.2.2 =
      some (package.literalRightSeamExactStage A strategy hwin key row past
        recordInput) :=
  rfl

/-- Unfolding an exact live stage reaches precisely the independently chosen
ordinary recurrent-bank root below the staged child. -/
@[simp] theorem literalRightSeamExactStageReversal_output_eq_recurrentRoot
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package) (row : PairedEntryRow)
    (past : List (In₁ × In₂)) (recordInput : In₁ × In₂)
    (input : In₁) :
    (package.literalRightSeamStagedReversalNoRecvOne A strategy hwin
      (package.literalRightSeamReceiverAtExactStage A strategy hwin key row
        past recordInput) input).1 =
      (package.literalRightSeamTaggedNoRecvOne A strategy hwin
        (package.literalRightSeamTaggedMatched A strategy hwin key row past
          recordInput).1 input).2 :=
  rfl

/-! ## The exact residual equation -/

/-- The one genuinely cross-construction equation required at a blind right
activation: the fresh mirror-table sender and the separately rationalized
ordinary recurrent root emit the same process-one output. -/
def LiteralCombinedFreshRightActivationRootBridge
    (package : Package A strategy hwin initial)
    (freshKey : Key A strategy hwin package)
    (stageKey : Key A strategy hwin package) (row : PairedEntryRow)
    (past : List (In₁ × In₂)) (recordInput : In₁ × In₂) : Prop :=
  ∀ input : In₁,
    (package.literalLeftSeamStagedSenderNoRecv A strategy hwin
        (package.literalLeftSeamStagedSenderInitial A strategy hwin freshKey)
        input).1 =
      (package.literalRightSeamTaggedNoRecvOne A strategy hwin
        (package.literalRightSeamTaggedMatched A strategy hwin stageKey row
          past recordInput).1 input).2

/-- Exact iff reduction of the live-stage pair test.  Everything around the
cross-rationalization output equality is definitional and kernel checked. -/
theorem literalCombinedFreshRight_pending_eq_exactStageReversal_iff
    (package : Package A strategy hwin initial)
    (fresh : FreshOne A strategy hwin (initial := initial))
    (freshKey : Key A strategy hwin package) (member : Bool)
    (stageKey : Key A strategy hwin package) (row : PairedEntryRow)
    (past : List (In₁ × In₂)) (recordInput : In₁ × In₂) :
    (∀ input : In₁,
      package.literalCombinedFreshRightPendingInitialOutput A strategy hwin
          fresh freshKey member input =
        (package.literalRightSeamStagedReversalNoRecvOne A strategy hwin
          (package.literalRightSeamReceiverAtExactStage A strategy hwin
            stageKey row past recordInput) input).1) ↔
      package.LiteralCombinedFreshRightActivationRootBridge A strategy hwin
        freshKey stageKey row past recordInput := by
  rfl

/-! ## What the shared preselection already proves -/

/-- At the fresh table, both hidden interpretations use one process-one
sender at every sender-local past.  This is the strongest unconditional
output equality furnished by the existing preselection construction. -/
theorem literalCombinedFreshRight_mirrorMembers_output_eq
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package) (past : List In₁) (input : In₁) :
    let table :=
      profiledRawJointLiteralLeftBothExactHeterogeneousRightTable A strategy
        hwin (package.literalLeftSeamInstalled A strategy hwin key)
    ((table.memberController false).labeledTree past).1 input =
      ((table.memberController true).labeledTree past).1 input := by
  exact
    profiledRawJointLiteralLeftBothExactHeterogeneousRightTable_noRecv_output_eq
      A strategy hwin (package.literalLeftSeamInstalled A strategy hwin key)
        past input

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
