/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshPhaseLiveReceiveTwo
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshPendingOnlyBoundary

/-!
# The corrected phase-live simultaneous close is synchronized

The retained-open process-one receive deliberately differs from the old
reset-on-every-receive map.  Its exact-close branch, however, still installs
the two fresh `.both,true` seam roots.  This file proves that those roots use
the very same leader-free boundary key as process two's mirror receive.

These are the two table clauses needed in the `both` field of the eventual
`ExactClosingSelectedTraceLaws`.  They use only the already proved freshness
alignment and boundary-key equations; no runtime orientation or leader bit is
introduced.
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

private abbrev LeftReceiver (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralLeftSeamStagedReceiverState A strategy
    hwin package

private abbrev LeftSender (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralLeftSeamStagedSenderState A strategy
    hwin package

/-! ## Mirror table alignment -/

/-- Mirror of `LiteralRightSeamStagedTableAligned`.  It records only local
table synchronization and the exact true member; the refreshed semantic stage
is intentionally not part of the relation. -/
def LiteralLeftSeamStagedTableAligned
    (package : Package A strategy hwin (initial := initial))
    (receiver : LeftReceiver A strategy hwin package)
    (sender : LeftSender A strategy hwin package) : Prop :=
  sender.1 = receiver.1 ∧
    HEq sender.2 receiver.2.2.1.2.1 ∧
    receiver.2.2.1.1 = true

/-- Fresh `.both,true` mirror roots are synchronized. -/
theorem literalLeftSeamStaged_initial_aligned
    (package : Package A strategy hwin (initial := initial))
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) :
    package.LiteralLeftSeamStagedTableAligned A strategy hwin
      (package.literalLeftSeamStagedReceiverInitial A strategy hwin key row
        true)
      (package.literalLeftSeamStagedSenderInitial A strategy hwin key) := by
  refine ⟨rfl, ?_, rfl⟩
  exact heq_of_eq
    (package.literalLeftSeamStaged_initial_controls_eq A strategy hwin key row
      true)

/-! ## The simultaneous boundary -/

/-- The corrected process-one closed right receiver and process two's freshly
installed right sender are the synchronized true-member roots at the common
boundary key. -/
theorem literalCombinedFreshPhaseLiveBoth_closed_right_aligned
    (package : Package A strategy hwin (initial := initial))
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package)
    (input : In₁ × In₂)
    (hfresh : DecoratedFreshnessAligned A strategy hwin one.2.1.1
      two.2.1.1) :
    package.LiteralRightSeamStagedTableAligned A strategy hwin
      (package.literalCombinedFreshOneReceiver A strategy hwin true
        (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
          input.1 two input.2).1.closedControl.2.1)
      (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two
        input.2 one input.1).1.closedControl.2.1.2.1 := by
  rw [package.literalCombinedFreshPhaseLiveRecvOne_closed_receiver A strategy
    hwin]
  change package.LiteralRightSeamStagedTableAligned A strategy hwin _
    (package.literalCombinedFreshTwoReceiveShared A strategy hwin two.2.1
      input.2 one.2.1 input.1).2.1
  rw [← package.literalCombinedFreshPendingBoundaryTwoShared_eq_receive_of_aligned
    A strategy hwin one.2.1 two.2.1 input hfresh]
  rw [package.literalCombinedFreshPendingBoundaryTwoShared_sender A strategy
    hwin]
  rw [package.literalCombinedFreshOneReceiveKey_eq_boundary A strategy hwin]
  exact package.literalRightSeamStaged_initial_aligned A strategy hwin
    (package.literalCombinedFreshPendingBoundaryKey A strategy hwin one.2.1
      two.2.1 input) .both

/-- The other half of the same close: process two's closed left receiver and
the corrected process-one freshly installed left sender are synchronized at
that identical boundary key. -/
theorem literalCombinedFreshPhaseLiveBoth_closed_left_aligned
    (package : Package A strategy hwin (initial := initial))
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package)
    (input : In₁ × In₂)
    (hfresh : DecoratedFreshnessAligned A strategy hwin one.2.1.1
      two.2.1.1) :
    package.LiteralLeftSeamStagedTableAligned A strategy hwin
      (package.literalCombinedFreshTwoReceiver A strategy hwin true
        (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two
          input.2 one input.1).1.closedControl.2.1)
      (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
        input.1 two input.2).1.closedControl.2.1.2.1 := by
  rw [package.literalCombinedFreshPhaseLiveRecvTwo_closed_receiver A strategy
    hwin]
  change package.LiteralLeftSeamStagedTableAligned A strategy hwin
    (package.literalCombinedFreshTwoReceiver A strategy hwin true
      (package.literalCombinedFreshTwoReceiveShared A strategy hwin two.2.1
        input.2 one.2.1 input.1))
    (package.literalLeftSeamStagedSenderInitial A strategy hwin
      (package.literalCombinedFreshOneReceiveKey A strategy hwin one.2.1
        input.1 two.2.1 input.2))
  rw [← package.literalCombinedFreshPendingBoundaryTwoShared_eq_receive_of_aligned
    A strategy hwin one.2.1 two.2.1 input hfresh]
  rw [package.literalCombinedFreshOneReceiveKey_eq_boundary A strategy hwin]
  exact package.literalLeftSeamStaged_initial_aligned A strategy hwin
    (package.literalCombinedFreshPendingBoundaryKey A strategy hwin one.2.1
      two.2.1 input) .both

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
