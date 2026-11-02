/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshPhaseLiveRootController
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralFalseAnchorFirstStepAudit

/-!
# Internal-anchor audit for the retained phase-live receivers

The outer deferred member is an acknowledgement-level choice and is reset to
`false` by an ordinary open receive.  The staged receiver nested inside the
shared value has a different Boolean: the member of the active heterogeneous
cross-anchor table.  That internal anchor is preserved by a table step and is
the only correct selector for the advanced receiver output.

This file exposes that fact without changing any active receive or controller
definition.  It also records the stage verdict.  False internal anchors are
reachable (already at the common root) and persist across a receive.  The old
staged constructor nevertheless reads the unused true product coordinate in
that case.  Thus reachability cannot justify assuming the anchor is true;
the false branch needs the branch-aware code-to-tag reconstruction.
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

private abbrev RightReceiver (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A strategy
    hwin package

private abbrev LeftReceiver (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralLeftSeamStagedReceiverState A strategy
    hwin package

private abbrev OneShared (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralCombinedFreshOneShared A strategy hwin
    package

private abbrev TwoShared (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoShared A strategy hwin
    package

private abbrev OnePending (package : Package A strategy hwin
    (initial := initial)) :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
    (OneShared A strategy hwin package)
    (ProfiledRawJointGuardedCommonLiteralCombinedFreshOnePayload A strategy
      hwin package)

private abbrev TwoPending (package : Package A strategy hwin
    (initial := initial)) :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
    (TwoShared A strategy hwin package)
    (ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoPayload A strategy
      hwin package)

/-! ## The two internal selectors -/

/-- Active heterogeneous-table member stored inside a right staged receiver. -/
def literalRightSeamStagedReceiverInternalAnchor
    {package : Package A strategy hwin (initial := initial)}
    (receiver : RightReceiver A strategy hwin package) : Bool :=
  receiver.2.2.1.1

/-- Mirror selector stored inside a left staged receiver. -/
def literalLeftSeamStagedReceiverInternalAnchor
    {package : Package A strategy hwin (initial := initial)}
    (receiver : LeftReceiver A strategy hwin package) : Bool :=
  receiver.2.2.1.1

@[simp] theorem literalRightSeamStagedReceiverInitial_internalAnchor
    (package : Package A strategy hwin (initial := initial))
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (anchor : Bool) :
    literalRightSeamStagedReceiverInternalAnchor A strategy hwin
        (package.literalRightSeamStagedReceiverInitial A strategy hwin key row
          anchor) =
      anchor :=
  rfl

@[simp] theorem literalLeftSeamStagedReceiverInitial_internalAnchor
    (package : Package A strategy hwin (initial := initial))
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (anchor : Bool) :
    literalLeftSeamStagedReceiverInternalAnchor A strategy hwin
        (package.literalLeftSeamStagedReceiverInitial A strategy hwin key row
          anchor) =
      anchor :=
  rfl

/-- One right-table receive preserves the internal table member. -/
@[simp] theorem literalRightSeamStagedReceiverRecv_internalAnchor
    (package : Package A strategy hwin (initial := initial))
    (receiver : RightReceiver A strategy hwin package)
    (own : In₁) (delivered : In₂) :
    literalRightSeamStagedReceiverInternalAnchor A strategy hwin
        (package.literalRightSeamStagedReceiverRecv A strategy hwin receiver
          own delivered).2 =
      literalRightSeamStagedReceiverInternalAnchor A strategy hwin receiver :=
  rfl

/-- Mirror preservation. -/
@[simp] theorem literalLeftSeamStagedReceiverRecv_internalAnchor
    (package : Package A strategy hwin (initial := initial))
    (receiver : LeftReceiver A strategy hwin package)
    (own : In₂) (delivered : In₁) :
    literalLeftSeamStagedReceiverInternalAnchor A strategy hwin
        (package.literalLeftSeamStagedReceiverRecv A strategy hwin receiver
          own delivered).2 =
      literalLeftSeamStagedReceiverInternalAnchor A strategy hwin receiver :=
  rfl

/-! ## The member-controller output actually advanced -/

/-- The raw right receiver output is precisely the receiver label of the
member controller selected by the receiver's internal anchor. -/
theorem literalRightSeamStagedReceiverRecv_output_eq_internalMemberLabel
    (package : Package A strategy hwin (initial := initial))
    (receiver : RightReceiver A strategy hwin package)
    (own : In₁) (delivered : In₂) :
    let result := package.literalRightSeamStagedReceiverRecv A strategy hwin
      receiver own delivered
    let table :=
      profiledRawJointLiteralRightBothExactHeterogeneousLeftTable A strategy
        hwin (package.literalRightSeamInstalled A strategy hwin receiver.1)
    result.1.2 =
      ((table.memberController
          (literalRightSeamStagedReceiverInternalAnchor A strategy hwin
            receiver)).labelOf receiver.2.2.1.2.1).2
        receiver.2.2.1.2.2 (own, delivered) :=
  rfl

/-- Left mirror of the member-label equation. -/
theorem literalLeftSeamStagedReceiverRecv_output_eq_internalMemberLabel
    (package : Package A strategy hwin (initial := initial))
    (receiver : LeftReceiver A strategy hwin package)
    (own : In₂) (delivered : In₁) :
    let result := package.literalLeftSeamStagedReceiverRecv A strategy hwin
      receiver own delivered
    let table :=
      profiledRawJointLiteralLeftBothExactHeterogeneousRightTable A strategy
        hwin (package.literalLeftSeamInstalled A strategy hwin receiver.1)
    result.1.2 =
      ((table.memberController
          (literalLeftSeamStagedReceiverInternalAnchor A strategy hwin
            receiver)).labelOf receiver.2.2.1.2.1).2
        receiver.2.2.1.2.2 (own, delivered) :=
  rfl

/-- Physical process-one projection at the internal member. -/
noncomputable def literalRightSeamInternalAnchorPhysicalOutput
    {package : Package A strategy hwin (initial := initial)}
    (receiver : RightReceiver A strategy hwin package)
    (output :
      ProfiledRawJointGuardedCommonLiteralRightSeamFrontReceiverOutput A
        strategy hwin package) : Out₁ :=
  if literalRightSeamStagedReceiverInternalAnchor A strategy hwin receiver then
    profiledRawJointTargetLeftReceiverBothPhysicalOutput output.2.2
  else
    profiledRawJointTargetLeftReceiverBothPhysicalOutput output.2.1

/-- Physical process-two mirror projection. -/
noncomputable def literalLeftSeamInternalAnchorPhysicalOutput
    {package : Package A strategy hwin (initial := initial)}
    (receiver : LeftReceiver A strategy hwin package)
    (output :
      ProfiledRawJointGuardedCommonLiteralLeftSeamFrontReceiverOutput A
        strategy hwin package) : Out₂ :=
  if literalLeftSeamStagedReceiverInternalAnchor A strategy hwin receiver then
    profiledRawJointTargetRightReceiverBothPhysicalOutput output.2.2
  else
    profiledRawJointTargetRightReceiverBothPhysicalOutput output.2.1

@[simp] theorem literalRightSeamInternalAnchorPhysicalOutput_false
    (package : Package A strategy hwin (initial := initial))
    (receiver : RightReceiver A strategy hwin package)
    (output :
      ProfiledRawJointGuardedCommonLiteralRightSeamFrontReceiverOutput A
        strategy hwin package)
    (hanchor : literalRightSeamStagedReceiverInternalAnchor A strategy hwin
      receiver = false) :
    literalRightSeamInternalAnchorPhysicalOutput A strategy hwin receiver
        output =
      profiledRawJointTargetLeftReceiverBothPhysicalOutput output.2.1 := by
  simp [literalRightSeamInternalAnchorPhysicalOutput, hanchor]

@[simp] theorem literalRightSeamInternalAnchorPhysicalOutput_true
    (package : Package A strategy hwin (initial := initial))
    (receiver : RightReceiver A strategy hwin package)
    (output :
      ProfiledRawJointGuardedCommonLiteralRightSeamFrontReceiverOutput A
        strategy hwin package)
    (hanchor : literalRightSeamStagedReceiverInternalAnchor A strategy hwin
      receiver = true) :
    literalRightSeamInternalAnchorPhysicalOutput A strategy hwin receiver
        output =
      profiledRawJointTargetLeftReceiverBothPhysicalOutput output.2.2 := by
  simp [literalRightSeamInternalAnchorPhysicalOutput, hanchor]

@[simp] theorem literalLeftSeamInternalAnchorPhysicalOutput_false
    (package : Package A strategy hwin (initial := initial))
    (receiver : LeftReceiver A strategy hwin package)
    (output :
      ProfiledRawJointGuardedCommonLiteralLeftSeamFrontReceiverOutput A
        strategy hwin package)
    (hanchor : literalLeftSeamStagedReceiverInternalAnchor A strategy hwin
      receiver = false) :
    literalLeftSeamInternalAnchorPhysicalOutput A strategy hwin receiver
        output =
      profiledRawJointTargetRightReceiverBothPhysicalOutput output.2.1 := by
  simp [literalLeftSeamInternalAnchorPhysicalOutput, hanchor]

@[simp] theorem literalLeftSeamInternalAnchorPhysicalOutput_true
    (package : Package A strategy hwin (initial := initial))
    (receiver : LeftReceiver A strategy hwin package)
    (output :
      ProfiledRawJointGuardedCommonLiteralLeftSeamFrontReceiverOutput A
        strategy hwin package)
    (hanchor : literalLeftSeamStagedReceiverInternalAnchor A strategy hwin
      receiver = true) :
    literalLeftSeamInternalAnchorPhysicalOutput A strategy hwin receiver
        output =
      profiledRawJointTargetRightReceiverBothPhysicalOutput output.2.2 := by
  simp [literalLeftSeamInternalAnchorPhysicalOutput, hanchor]

/-! ## False is genuinely reachable -/

/-- The common rooted process-one live receiver starts in member `false`. -/
@[simp] theorem literalCombinedFreshPhaseLiveRootRightInternalAnchor
    (package : Package A strategy hwin (initial := initial)) :
    literalRightSeamStagedReceiverInternalAnchor A strategy hwin
        (package.literalCombinedFreshLiveRightReceiverForRecvOne A strategy
          hwin
          (package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin)
          (package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin)) =
      false :=
  rfl

/-- The mirror live receiver also starts in member `false`. -/
@[simp] theorem literalCombinedFreshPhaseLiveRootLeftInternalAnchor
    (package : Package A strategy hwin (initial := initial)) :
    literalLeftSeamStagedReceiverInternalAnchor A strategy hwin
        (package.literalCombinedFreshLiveLeftReceiverForRecvTwo A strategy
          hwin
          (package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin)
          (package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin)) =
      false :=
  rfl

/-- An ordinary phase-live process-one receive retains the internal anchor,
even though its returned outer deferred member is definitionally `false`. -/
theorem literalCombinedFreshPhaseLiveRecvOne_open_internalAnchor
    (package : Package A strategy hwin (initial := initial))
    (one : OnePending A strategy hwin package) (own : In₁)
    (two : TwoPending A strategy hwin package) (delivered : In₂) :
    literalRightSeamStagedReceiverInternalAnchor A strategy hwin
        (package.literalCombinedFreshOneReceiver A strategy hwin false
          (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one own
            two delivered).1.openControl.2.1) =
      literalRightSeamStagedReceiverInternalAnchor A strategy hwin
        (package.literalCombinedFreshLiveRightReceiverForRecvOne A strategy
          hwin one two) :=
  rfl

/-- Process-two mirror. -/
theorem literalCombinedFreshPhaseLiveRecvTwo_open_internalAnchor
    (package : Package A strategy hwin (initial := initial))
    (two : TwoPending A strategy hwin package) (own : In₂)
    (one : OnePending A strategy hwin package) (delivered : In₁) :
    literalLeftSeamStagedReceiverInternalAnchor A strategy hwin
        (package.literalCombinedFreshTwoReceiver A strategy hwin false
          (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two own
            one delivered).1.openControl.2.1) =
      literalLeftSeamStagedReceiverInternalAnchor A strategy hwin
        (package.literalCombinedFreshLiveLeftReceiverForRecvTwo A strategy
          hwin two one) :=
  rfl

/-- The closed process-one receiver is the true member root. -/
@[simp] theorem literalCombinedFreshPhaseLiveRecvOne_closed_internalAnchor
    (package : Package A strategy hwin (initial := initial))
    (one : OnePending A strategy hwin package) (own : In₁)
    (two : TwoPending A strategy hwin package) (delivered : In₂) :
    literalRightSeamStagedReceiverInternalAnchor A strategy hwin
        (package.literalCombinedFreshOneReceiver A strategy hwin true
          (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one own
            two delivered).1.closedControl.2.1) =
      true :=
  rfl

/-- Mirror closed receiver. -/
@[simp] theorem literalCombinedFreshPhaseLiveRecvTwo_closed_internalAnchor
    (package : Package A strategy hwin (initial := initial))
    (two : TwoPending A strategy hwin package) (own : In₂)
    (one : OnePending A strategy hwin package) (delivered : In₁) :
    literalLeftSeamStagedReceiverInternalAnchor A strategy hwin
        (package.literalCombinedFreshTwoReceiver A strategy hwin true
          (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two own
            one delivered).1.closedControl.2.1) =
      true :=
  rfl

/-! ## Honest stage verdict -/

/-- On the false first right member, obtaining the canonical exact stage is
equivalent to identifying the unused true output coordinate with the tagged
target.  The active false monitor does not supply this equality. -/
theorem literalRightSeamFalseInternalAnchor_stage_residual
    (package : Package A strategy hwin (initial := initial))
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (input : In₁ × In₂) :
    let result := package.literalRightSeamStagedFirstRound A strategy hwin key
      row false input
    result.2.1.2.2.2 =
        some (package.literalRightSeamExactStage A strategy hwin key row []
          input) ↔
      package.literalRightSeamStagedFirstRoundChild A strategy hwin key row
          false input =
        package.literalRightSeamTaggedTarget A strategy hwin key row []
          input :=
  package.literalRightSeamStagedFirstRound_false_stage_eq_exact_iff A strategy
    hwin key row input

/-- Left mirror of the false-anchor residual. -/
theorem literalLeftSeamFalseInternalAnchor_stage_residual
    (package : Package A strategy hwin (initial := initial))
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (input : In₂ × In₁) :
    let result := package.literalLeftSeamStagedFirstRound A strategy hwin key
      row false input
    result.2.1.2.2.2 =
        some (package.literalLeftSeamExactStage A strategy hwin key row []
          input) ↔
      package.literalLeftSeamStagedFirstRoundChild A strategy hwin key row
          false input =
        package.literalLeftSeamTaggedTarget A strategy hwin key row [] input :=
  package.literalLeftSeamStagedFirstRound_false_stage_eq_exact_iff A strategy
    hwin key row input

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
