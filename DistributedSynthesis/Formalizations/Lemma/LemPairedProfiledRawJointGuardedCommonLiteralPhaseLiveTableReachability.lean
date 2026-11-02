/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteCrossAnchorLocalCarrierReachability
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshPhaseLiveTraceInvariant

/-!
# Root-prefix witnesses for phase-live seam tables

The structural phase-live invariant synchronizes endpoint controls, but that
alone does not say that the controls lie on a play starting at the selected
table root.  Here we retain the missing fact as a proof-side prefix witness.
It is seeded at every seam installation and extended by each homogeneous
local round.  No prefix, graph, orientation, or leader flag is added to an
executable state.
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

private abbrev RightSender (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamStagedSenderState A strategy
    hwin package

private abbrev LeftReceiver (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralLeftSeamStagedReceiverState A strategy
    hwin package

private abbrev LeftSender (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralLeftSeamStagedSenderState A strategy
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

private abbrev OneControl (package : Package A strategy hwin
    (initial := initial)) :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (OneShared A strategy hwin package)
    (ProfiledRawJointGuardedCommonLiteralCombinedFreshOnePayload A strategy
      hwin package) Unit

private abbrev TwoControl (package : Package A strategy hwin
    (initial := initial)) :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (TwoShared A strategy hwin package)
    (ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoPayload A strategy
      hwin package) Unit

/-! ## Right seam -/

/-- The staged right-seam endpoints are the table states reached by one
common strict-left input prefix.  Row and latest exact stage are orthogonal
to this table reachability witness. -/
def LiteralRightSeamTableRootReachable
    (package : Package A strategy hwin (initial := initial))
    (receiver : RightReceiver A strategy hwin package)
    (sender : RightSender A strategy hwin package) : Prop :=
  ∃ past : List (In₁ × In₂),
    sender =
      ⟨receiver.1,
        finiteCrossAnchorSenderAtPrefix
          (profiledRawJointLiteralRightBothExactHeterogeneousLeftTable A
            strategy hwin
            (package.literalRightSeamInstalled A strategy hwin receiver.1))
          past⟩ ∧
    receiver.2.2.1 =
      finiteCrossAnchorReceiverAtPrefix
        (profiledRawJointLiteralRightBothExactHeterogeneousLeftTable A strategy
          hwin
          (package.literalRightSeamInstalled A strategy hwin receiver.1))
        receiver.2.2.1.1 past

/-- Every staged right-seam installation is a member-table root. -/
theorem literalRightSeamTableRootReachable_initial
    (package : Package A strategy hwin (initial := initial))
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (anchor : Bool) :
    package.LiteralRightSeamTableRootReachable A strategy hwin
      (package.literalRightSeamStagedReceiverInitial A strategy hwin key row
        anchor)
      (package.literalRightSeamStagedSenderInitial A strategy hwin key) := by
  refine ⟨[], ?_, ?_⟩
  · rfl
  · rfl

/-- One homogeneous left round extends the right table's root-prefix
witness. -/
theorem LiteralRightSeamTableRootReachable.step
    (package : Package A strategy hwin (initial := initial))
    {receiver : RightReceiver A strategy hwin package}
    {sender : RightSender A strategy hwin package}
    (hreach : package.LiteralRightSeamTableRootReachable A strategy hwin
      receiver sender)
    (input : In₁ × In₂) :
    package.LiteralRightSeamTableRootReachable A strategy hwin
      (package.literalRightSeamBranchStagedReceiverRecv A strategy hwin
        receiver input.1 input.2).2
      (package.literalRightSeamStagedSenderNoRecv A strategy hwin sender
        input.2).2 := by
  rcases hreach with ⟨past, hsender, hreceiver⟩
  rcases receiver with ⟨key, row, tableReceiver, stage⟩
  dsimp only at hsender hreceiver ⊢
  subst sender
  rw [hreceiver]
  let table :=
    profiledRawJointLiteralRightBothExactHeterogeneousLeftTable A strategy
      hwin (package.literalRightSeamInstalled A strategy hwin key)
  refine ⟨past ++ [input], ?_, ?_⟩
  · apply Sigma.ext
    · rfl
    · simpa [literalRightSeamStagedSenderNoRecv,
        literalRightSeamFrontSenderNoRecv,
        profiledRawJointLiteralRightBothExactSenderNoRecv,
        literalRightSeamBranchStagedReceiverRecv, table] using
          (finiteCrossAnchorSenderNoRecv_atPrefix table past input)
  · simp only [literalRightSeamBranchStagedReceiverRecv]
    exact finiteCrossAnchorReceiverRecv_atPrefix table _ past input

/-- A repeated strict-left round preserves the witnessed right-table root
prefix. -/
theorem literalCombinedFreshPhaseLiveRecvOne_same_reachable
    (package : Package A strategy hwin (initial := initial))
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package)
    (hphase : one.2.1.1.2 = true)
    (hreach : package.LiteralRightSeamTableRootReachable A strategy hwin
      (package.literalCombinedFreshOneReceiver A strategy hwin one.1
        one.2.1) two.2.1.2.1)
    (input : In₁ × In₂) :
    package.LiteralRightSeamTableRootReachable A strategy hwin
      (package.literalCombinedFreshOneReceiver A strategy hwin false
        (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
          input.1 two input.2).1.openControl.2.1)
      (package.literalRightSeamStagedSenderNoRecv A strategy hwin
        two.2.1.2.1 input.2).2 := by
  rw [package.literalCombinedFreshPhaseLiveRecvOne_open_receiver A strategy
    hwin]
  rw [package.literalCombinedFreshLiveRightReceiverForRecvOne_same A strategy
    hwin one two hphase]
  exact LiteralRightSeamTableRootReachable.step A strategy hwin package hreach
    input

/-- At a right-to-left switch the dormant sender root and freshly initialized
receiver execute the first record of a new witnessed table prefix. -/
theorem literalCombinedFreshPhaseLiveRecvOne_switch_reachable
    (package : Package A strategy hwin (initial := initial))
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package)
    (hphase : one.2.1.1.2 = false)
    (hroot : two.2.1.2.1 =
      package.literalRightSeamStagedSenderInitial A strategy hwin
        two.2.1.2.1.1)
    (input : In₁ × In₂) :
    package.LiteralRightSeamTableRootReachable A strategy hwin
      (package.literalCombinedFreshOneReceiver A strategy hwin false
        (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
          input.1 two input.2).1.openControl.2.1)
      (package.literalRightSeamStagedSenderNoRecv A strategy hwin
        two.2.1.2.1 input.2).2 := by
  rw [package.literalCombinedFreshPhaseLiveRecvOne_open_receiver A strategy
    hwin]
  rw [package.literalCombinedFreshLiveRightReceiverForRecvOne_switch A
    strategy hwin one two hphase]
  rw [hroot]
  exact LiteralRightSeamTableRootReachable.step A strategy hwin package
    (package.literalRightSeamTableRootReachable_initial A strategy hwin
      two.2.1.2.1.1 (literalCombinedFreshRowOfMember two.1) two.1) input

/-! ## Left seam -/

/-- Mirror root-prefix witness for the strict-right seam. -/
def LiteralLeftSeamTableRootReachable
    (package : Package A strategy hwin (initial := initial))
    (receiver : LeftReceiver A strategy hwin package)
    (sender : LeftSender A strategy hwin package) : Prop :=
  ∃ past : List (In₂ × In₁),
    sender =
      ⟨receiver.1,
        finiteCrossAnchorSenderAtPrefix
          (profiledRawJointLiteralLeftBothExactHeterogeneousRightTable A
            strategy hwin
            (package.literalLeftSeamInstalled A strategy hwin receiver.1))
          past⟩ ∧
    receiver.2.2.1 =
      finiteCrossAnchorReceiverAtPrefix
        (profiledRawJointLiteralLeftBothExactHeterogeneousRightTable A strategy
          hwin
          (package.literalLeftSeamInstalled A strategy hwin receiver.1))
        receiver.2.2.1.1 past

theorem literalLeftSeamTableRootReachable_initial
    (package : Package A strategy hwin (initial := initial))
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (anchor : Bool) :
    package.LiteralLeftSeamTableRootReachable A strategy hwin
      (package.literalLeftSeamStagedReceiverInitial A strategy hwin key row
        anchor)
      (package.literalLeftSeamStagedSenderInitial A strategy hwin key) := by
  refine ⟨[], ?_, ?_⟩
  · rfl
  · rfl

theorem LiteralLeftSeamTableRootReachable.step
    (package : Package A strategy hwin (initial := initial))
    {receiver : LeftReceiver A strategy hwin package}
    {sender : LeftSender A strategy hwin package}
    (hreach : package.LiteralLeftSeamTableRootReachable A strategy hwin
      receiver sender)
    (input : In₂ × In₁) :
    package.LiteralLeftSeamTableRootReachable A strategy hwin
      (package.literalLeftSeamBranchStagedReceiverRecv A strategy hwin
        receiver input.1 input.2).2
      (package.literalLeftSeamStagedSenderNoRecv A strategy hwin sender
        input.2).2 := by
  rcases hreach with ⟨past, hsender, hreceiver⟩
  rcases receiver with ⟨key, row, tableReceiver, stage⟩
  dsimp only at hsender hreceiver ⊢
  subst sender
  rw [hreceiver]
  let table :=
    profiledRawJointLiteralLeftBothExactHeterogeneousRightTable A strategy
      hwin (package.literalLeftSeamInstalled A strategy hwin key)
  refine ⟨past ++ [input], ?_, ?_⟩
  · apply Sigma.ext
    · rfl
    · simpa [literalLeftSeamStagedSenderNoRecv,
        literalLeftSeamFrontSenderNoRecv,
        profiledRawJointLiteralLeftBothExactSenderNoRecv,
        literalLeftSeamBranchStagedReceiverRecv, table] using
          (finiteCrossAnchorSenderNoRecv_atPrefix table past input)
  · simp only [literalLeftSeamBranchStagedReceiverRecv]
    exact finiteCrossAnchorReceiverRecv_atPrefix table _ past input

/-- Repeated strict-right step of the mirror witness. -/
theorem literalCombinedFreshPhaseLiveRecvTwo_same_reachable
    (package : Package A strategy hwin (initial := initial))
    (two : TwoPending A strategy hwin package)
    (one : OnePending A strategy hwin package)
    (hphase : two.2.1.1.2 = false)
    (hreach : package.LiteralLeftSeamTableRootReachable A strategy hwin
      (package.literalCombinedFreshTwoReceiver A strategy hwin two.1
        two.2.1) one.2.1.2.1)
    (input : In₁ × In₂) :
    package.LiteralLeftSeamTableRootReachable A strategy hwin
      (package.literalCombinedFreshTwoReceiver A strategy hwin false
        (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two
          input.2 one input.1).1.openControl.2.1)
      (package.literalLeftSeamStagedSenderNoRecv A strategy hwin
        one.2.1.2.1 input.1).2 := by
  rw [package.literalCombinedFreshPhaseLiveRecvTwo_open_receiver A strategy
    hwin]
  rw [package.literalCombinedFreshLiveLeftReceiverForRecvTwo_same A strategy
    hwin two one hphase]
  exact LiteralLeftSeamTableRootReachable.step A strategy hwin package hreach
    (input.2, input.1)

/-- Left-to-right switch seeds and immediately extends the mirror witness. -/
theorem literalCombinedFreshPhaseLiveRecvTwo_switch_reachable
    (package : Package A strategy hwin (initial := initial))
    (two : TwoPending A strategy hwin package)
    (one : OnePending A strategy hwin package)
    (hphase : two.2.1.1.2 = true)
    (hroot : one.2.1.2.1 =
      package.literalLeftSeamStagedSenderInitial A strategy hwin
        one.2.1.2.1.1)
    (input : In₁ × In₂) :
    package.LiteralLeftSeamTableRootReachable A strategy hwin
      (package.literalCombinedFreshTwoReceiver A strategy hwin false
        (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two
          input.2 one input.1).1.openControl.2.1)
      (package.literalLeftSeamStagedSenderNoRecv A strategy hwin
        one.2.1.2.1 input.1).2 := by
  rw [package.literalCombinedFreshPhaseLiveRecvTwo_open_receiver A strategy
    hwin]
  rw [package.literalCombinedFreshLiveLeftReceiverForRecvTwo_switch A
    strategy hwin two one hphase]
  rw [hroot]
  exact LiteralLeftSeamTableRootReachable.step A strategy hwin package
    (package.literalLeftSeamTableRootReachable_initial A strategy hwin
      one.2.1.2.1.1 (literalCombinedFreshRowOfMember one.1) one.1)
    (input.2, input.1)

/-! ## Phase-dependent global witness -/

/-- The table(s) currently synchronized by the local phase carry genuine
root-prefix witnesses.  At the simultaneous phase both tables do. -/
def LiteralCombinedFreshPhaseLiveTableRootReachable
    (package : Package A strategy hwin (initial := initial))
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package) : Prop :=
  match one.2.1.1.2, two.2.1.1.2 with
  | false, false =>
      package.LiteralLeftSeamTableRootReachable A strategy hwin
        (package.literalCombinedFreshTwoReceiver A strategy hwin two.1
          two.2.1) one.2.1.2.1
  | true, true =>
      package.LiteralRightSeamTableRootReachable A strategy hwin
        (package.literalCombinedFreshOneReceiver A strategy hwin one.1
          one.2.1) two.2.1.2.1
  | true, false =>
      package.LiteralRightSeamTableRootReachable A strategy hwin
          (package.literalCombinedFreshOneReceiver A strategy hwin one.1
            one.2.1) two.2.1.2.1 ∧
        package.LiteralLeftSeamTableRootReachable A strategy hwin
          (package.literalCombinedFreshTwoReceiver A strategy hwin two.1
            two.2.1) one.2.1.2.1
  | false, true => False

/-- Structural selection strengthened only by the proof-side root-prefix
witness. -/
def LiteralCombinedFreshPhaseLiveRootReachableSelected
    (package : Package A strategy hwin (initial := initial))
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package) : Prop :=
  package.LiteralCombinedFreshPhaseLiveStructuralSelected A strategy hwin one
      two ∧
    package.LiteralCombinedFreshPhaseLiveTableRootReachable A strategy hwin one
      two

/-- The common phase-live root carries both table root witnesses. -/
theorem literalCombinedFreshPhaseLiveRootReachableSelected_initial
    (package : Package A strategy hwin (initial := initial)) :
    package.LiteralCombinedFreshPhaseLiveRootReachableSelected A strategy hwin
      (package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin)
      (package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin) := by
  refine ⟨package.literalCombinedFreshPhaseLiveStructuralSelected_initial A
    strategy hwin, ?_⟩
  change
    package.LiteralRightSeamTableRootReachable A strategy hwin
        (package.literalRightSeamStagedReceiverInitial A strategy hwin
          (package.literalCombinedFreshPendingOnlyInitialKey A strategy hwin)
          .first false)
        (package.literalRightSeamStagedSenderInitial A strategy hwin
          (package.literalCombinedFreshPendingOnlyInitialKey A strategy hwin)) ∧
      package.LiteralLeftSeamTableRootReachable A strategy hwin
        (package.literalLeftSeamStagedReceiverInitial A strategy hwin
          (package.literalCombinedFreshPendingOnlyInitialKey A strategy hwin)
          .first false)
        (package.literalLeftSeamStagedSenderInitial A strategy hwin
          (package.literalCombinedFreshPendingOnlyInitialKey A strategy hwin))
  exact ⟨
    package.literalRightSeamTableRootReachable_initial A strategy hwin _ .first
      false,
    package.literalLeftSeamTableRootReachable_initial A strategy hwin _ .first
      false⟩

/-! ## Fresh simultaneous roots -/

theorem literalCombinedFreshPhaseLiveBoth_closed_right_reachable
    (package : Package A strategy hwin (initial := initial))
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package)
    (input : In₁ × In₂)
    (hfresh : DecoratedFreshnessAligned A strategy hwin one.2.1.1
      two.2.1.1) :
    package.LiteralRightSeamTableRootReachable A strategy hwin
      (package.literalCombinedFreshOneReceiver A strategy hwin true
        (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
          input.1 two input.2).1.closedControl.2.1)
      (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two
        input.2 one input.1).1.closedControl.2.1.2.1 := by
  rw [package.literalCombinedFreshPhaseLiveRecvOne_closed_receiver A strategy
    hwin]
  change package.LiteralRightSeamTableRootReachable A strategy hwin _
    (package.literalCombinedFreshTwoReceiveShared A strategy hwin two.2.1
      input.2 one.2.1 input.1).2.1
  rw [← package.literalCombinedFreshPendingBoundaryTwoShared_eq_receive_of_aligned
    A strategy hwin one.2.1 two.2.1 input hfresh]
  rw [package.literalCombinedFreshPendingBoundaryTwoShared_sender A strategy
    hwin]
  rw [package.literalCombinedFreshOneReceiveKey_eq_boundary A strategy hwin]
  exact package.literalRightSeamTableRootReachable_initial A strategy hwin
    (package.literalCombinedFreshPendingBoundaryKey A strategy hwin one.2.1
      two.2.1 input) .both true

theorem literalCombinedFreshPhaseLiveBoth_closed_left_reachable
    (package : Package A strategy hwin (initial := initial))
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package)
    (input : In₁ × In₂)
    (hfresh : DecoratedFreshnessAligned A strategy hwin one.2.1.1
      two.2.1.1) :
    package.LiteralLeftSeamTableRootReachable A strategy hwin
      (package.literalCombinedFreshTwoReceiver A strategy hwin true
        (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two
          input.2 one input.1).1.closedControl.2.1)
      (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
        input.1 two input.2).1.closedControl.2.1.2.1 := by
  rw [package.literalCombinedFreshPhaseLiveRecvTwo_closed_receiver A strategy
    hwin]
  change package.LiteralLeftSeamTableRootReachable A strategy hwin
    (package.literalCombinedFreshTwoReceiver A strategy hwin true
      (package.literalCombinedFreshTwoReceiveShared A strategy hwin two.2.1
        input.2 one.2.1 input.1))
    (package.literalLeftSeamStagedSenderInitial A strategy hwin
      (package.literalCombinedFreshOneReceiveKey A strategy hwin one.2.1
        input.1 two.2.1 input.2))
  rw [← package.literalCombinedFreshPendingBoundaryTwoShared_eq_receive_of_aligned
    A strategy hwin one.2.1 two.2.1 input hfresh]
  rw [package.literalCombinedFreshOneReceiveKey_eq_boundary A strategy hwin]
  exact package.literalLeftSeamTableRootReachable_initial A strategy hwin
    (package.literalCombinedFreshPendingBoundaryKey A strategy hwin one.2.1
      two.2.1 input) .both true

/-! ## Preservation by the rooted phase-live transition -/

theorem literalCombinedFreshPhaseLiveRootReachableSelected_both
    (package : Package A strategy hwin (initial := initial))
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package)
    (hselected :
      package.LiteralCombinedFreshPhaseLiveRootReachableSelected A strategy
        hwin one two)
    (input : In₁ × In₂) :
    let oneNext :=
      (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
        input.1 two input.2).1.closedControl
    let twoNext :=
      (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two
        input.2 one input.1).1.closedControl
    package.LiteralCombinedFreshPhaseLiveRootReachableSelected A strategy hwin
      oneNext twoNext := by
  dsimp only
  refine ⟨
    package.literalCombinedFreshPhaseLiveStructuralSelected_both A strategy
      hwin one two hselected.1 input,
    ?_⟩
  change
    package.LiteralRightSeamTableRootReachable A strategy hwin
        (package.literalCombinedFreshOneReceiver A strategy hwin true
          (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
            input.1 two input.2).1.closedControl.2.1)
        (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two
          input.2 one input.1).1.closedControl.2.1.2.1 ∧
      package.LiteralLeftSeamTableRootReachable A strategy hwin
        (package.literalCombinedFreshTwoReceiver A strategy hwin true
          (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two
            input.2 one input.1).1.closedControl.2.1)
        (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
          input.1 two input.2).1.closedControl.2.1.2.1
  exact ⟨
    package.literalCombinedFreshPhaseLiveBoth_closed_right_reachable A
      strategy hwin one two input hselected.1.1,
    package.literalCombinedFreshPhaseLiveBoth_closed_left_reachable A strategy
      hwin one two input hselected.1.1⟩

theorem literalCombinedFreshPhaseLiveRootReachableSelected_strictRight
    (package : Package A strategy hwin (initial := initial))
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package)
    (hselected :
      package.LiteralCombinedFreshPhaseLiveRootReachableSelected A strategy
        hwin one two)
    (input : In₁ × In₂) :
    let oneNext := FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
      (package.literalCombinedFreshOnePendingStep A strategy hwin) one input.1
    let twoNext :=
      (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two
        input.2 one input.1).1.openControl
    package.LiteralCombinedFreshPhaseLiveRootReachableSelected A strategy hwin
      oneNext.1 twoNext := by
  dsimp only
  rcases hselected with ⟨⟨hfresh, hpolicy, htables⟩, hreach⟩
  refine ⟨
    package.literalCombinedFreshPhaseLiveStructuralSelected_strictRight A
      strategy hwin one two ⟨hfresh, hpolicy, htables⟩ input,
    ?_⟩
  change package.LiteralLeftSeamTableRootReachable A strategy hwin
    (package.literalCombinedFreshTwoReceiver A strategy hwin false
      (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two
        input.2 one input.1).1.openControl.2.1)
    (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
      (package.literalCombinedFreshOnePendingStep A strategy hwin) one
        input.1).1.2.1.2.1
  cases hone : one.2.1.1.2 <;> cases htwo : two.2.1.1.2
  · simp only [LiteralCombinedFreshPhaseLiveTableRootReachable, hone, htwo]
      at hreach
    exact package.literalCombinedFreshPhaseLiveRecvTwo_same_reachable A
      strategy hwin two one htwo hreach input
  · simp only [LiteralCombinedFreshPhaseLiveTableRootReachable, hone, htwo]
      at hreach
  · simp only [LiteralCombinedFreshPhaseLiveTableRootReachable, hone, htwo]
      at hreach
    exact package.literalCombinedFreshPhaseLiveRecvTwo_same_reachable A
      strategy hwin two one htwo hreach.2 input
  · simp only [LiteralCombinedFreshPhaseLiveTableRootReachable, hone, htwo]
      at hreach
    simp only [LiteralCombinedFreshPhaseLiveTableInvariant, hone, htwo] at htables
    exact package.literalCombinedFreshPhaseLiveRecvTwo_switch_reachable A
      strategy hwin two one htwo htables.2 input

theorem literalCombinedFreshPhaseLiveRootReachableSelected_strictLeft
    (package : Package A strategy hwin (initial := initial))
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package)
    (hselected :
      package.LiteralCombinedFreshPhaseLiveRootReachableSelected A strategy
        hwin one two)
    (input : In₁ × In₂) :
    let oneNext :=
      (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
        input.1 two input.2).1.openControl
    let twoNext := FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
      (package.literalCombinedFreshTwoPendingStep A strategy hwin) two input.2
    package.LiteralCombinedFreshPhaseLiveRootReachableSelected A strategy hwin
      oneNext twoNext.1 := by
  dsimp only
  rcases hselected with ⟨⟨hfresh, hpolicy, htables⟩, hreach⟩
  refine ⟨
    package.literalCombinedFreshPhaseLiveStructuralSelected_strictLeft A
      strategy hwin one two ⟨hfresh, hpolicy, htables⟩ input,
    ?_⟩
  change package.LiteralRightSeamTableRootReachable A strategy hwin
    (package.literalCombinedFreshOneReceiver A strategy hwin false
      (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
        input.1 two input.2).1.openControl.2.1)
    (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
      (package.literalCombinedFreshTwoPendingStep A strategy hwin) two
        input.2).1.2.1.2.1
  cases hone : one.2.1.1.2 <;> cases htwo : two.2.1.1.2
  · simp only [LiteralCombinedFreshPhaseLiveTableRootReachable, hone, htwo]
      at hreach
    simp only [LiteralCombinedFreshPhaseLiveTableInvariant, hone, htwo] at htables
    exact package.literalCombinedFreshPhaseLiveRecvOne_switch_reachable A
      strategy hwin one two hone htables.2 input
  · simp only [LiteralCombinedFreshPhaseLiveTableRootReachable, hone, htwo]
      at hreach
  · simp only [LiteralCombinedFreshPhaseLiveTableRootReachable, hone, htwo]
      at hreach
    exact package.literalCombinedFreshPhaseLiveRecvOne_same_reachable A
      strategy hwin one two hone hreach.1 input
  · simp only [LiteralCombinedFreshPhaseLiveTableRootReachable, hone, htwo]
      at hreach
    exact package.literalCombinedFreshPhaseLiveRecvOne_same_reachable A
      strategy hwin one two hone hreach input

/-! ## Pointwise witnessed semantic trace -/

/-- Canonical selection strengthened by genuine member-controller root
reachability. -/
def LiteralCombinedFreshPhaseLiveCanonicalRootReachableSelected
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂)
    (one : OneControl A strategy hwin package)
    (two : TwoControl A strategy hwin package) (n : Nat) : Prop :=
  ∃ onePending : OnePending A strategy hwin package,
    ∃ twoPending : TwoPending A strategy hwin package,
      one = .inl onePending ∧ two = .inl twoPending ∧
        package.LiteralCombinedFreshPhaseLiveRootReachableSelected A strategy
          hwin onePending twoPending ∧
        (one, two) =
          package.literalCombinedFreshPhaseLiveRootSemanticTrace A strategy
            hwin env n

/-- Every pair on the canonical phase-live semantic run carries the exact
root-prefix witness required to read its active local round as a suffix of a
winning heterogeneous member play. -/
theorem literalCombinedFreshPhaseLiveRootSemanticTrace_rootReachable
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) : ∀ n : Nat,
    package.LiteralCombinedFreshPhaseLiveCanonicalRootReachableSelected A
      strategy hwin env
      (package.literalCombinedFreshPhaseLiveRootSemanticTrace A strategy hwin
        env n).1
      (package.literalCombinedFreshPhaseLiveRootSemanticTrace A strategy hwin
        env n).2 n := by
  intro n
  induction n with
  | zero =>
      exact ⟨
        package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin,
        package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin,
        rfl, rfl,
        package.literalCombinedFreshPhaseLiveRootReachableSelected_initial A
          strategy hwin,
        rfl⟩
  | succ n ih =>
      rcases ih with
        ⟨onePending, twoPending, hone, htwo, hselected, hcanonical⟩
      have hpair :
          ((.inl onePending : OneControl A strategy hwin package),
            (.inl twoPending : TwoControl A strategy hwin package)) =
            package.literalCombinedFreshPhaseLiveRootSemanticTrace A strategy
              hwin env n := by
        apply Prod.ext
        · exact hone.symm
        · exact htwo.symm
      have hcanonicalSelected :
          package.LiteralCombinedFreshPhaseLiveCanonicalSelected A strategy
            hwin env (.inl onePending) (.inl twoPending) n :=
        ⟨onePending, twoPending, rfl, rfl, hselected.1, hpair⟩
      cases hgraph : (env n).graph with
      | right =>
          let oneNext : OnePending A strategy hwin package :=
            (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
              (package.literalCombinedFreshOnePendingStep A strategy hwin)
              onePending (env n).inputOne).1
          let twoNext : TwoPending A strategy hwin package :=
            (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin
              twoPending (env n).inputTwo onePending (env n).inputOne
              ).1.openControl
          have hnext :=
            package.literalCombinedFreshPhaseLiveRootReachableSelected_strictRight
              A strategy hwin onePending twoPending hselected
                ((env n).inputOne, (env n).inputTwo)
          have hpairNext :
              ((.inl oneNext : OneControl A strategy hwin package),
                (.inl twoNext : TwoControl A strategy hwin package)) =
                package.literalCombinedFreshPhaseLiveRootSemanticTrace A
                  strategy hwin env (n + 1) := by
            have hnextCanonical :=
              (package.literalCombinedFreshPhaseLiveRootSelectedTraceLaws A
                strategy hwin env).strictRight n (.inl onePending)
                  (.inl twoPending) trivial hcanonicalSelected hgraph |>.1
            rcases hnextCanonical with ⟨_, _, _, _, _, htraceNext⟩
            exact htraceNext
          exact ⟨oneNext, twoNext,
            (congrArg Prod.fst hpairNext).symm,
            (congrArg Prod.snd hpairNext).symm, hnext, rfl⟩
      | left =>
          let oneNext : OnePending A strategy hwin package :=
            (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin
              onePending (env n).inputOne twoPending (env n).inputTwo
              ).1.openControl
          let twoNext : TwoPending A strategy hwin package :=
            (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
              (package.literalCombinedFreshTwoPendingStep A strategy hwin)
              twoPending (env n).inputTwo).1
          have hnext :=
            package.literalCombinedFreshPhaseLiveRootReachableSelected_strictLeft
              A strategy hwin onePending twoPending hselected
                ((env n).inputOne, (env n).inputTwo)
          have hpairNext :
              ((.inl oneNext : OneControl A strategy hwin package),
                (.inl twoNext : TwoControl A strategy hwin package)) =
                package.literalCombinedFreshPhaseLiveRootSemanticTrace A
                  strategy hwin env (n + 1) := by
            have hnextCanonical :=
              (package.literalCombinedFreshPhaseLiveRootSelectedTraceLaws A
                strategy hwin env).strictLeft n (.inl onePending)
                  (.inl twoPending) trivial hcanonicalSelected hgraph |>.1
            rcases hnextCanonical with ⟨_, _, _, _, _, htraceNext⟩
            exact htraceNext
          exact ⟨oneNext, twoNext,
            (congrArg Prod.fst hpairNext).symm,
            (congrArg Prod.snd hpairNext).symm, hnext, rfl⟩
      | both =>
          let oneNext : OnePending A strategy hwin package :=
            (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin
              onePending (env n).inputOne twoPending (env n).inputTwo
              ).1.closedControl
          let twoNext : TwoPending A strategy hwin package :=
            (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin
              twoPending (env n).inputTwo onePending (env n).inputOne
              ).1.closedControl
          have hnext :=
            package.literalCombinedFreshPhaseLiveRootReachableSelected_both A
              strategy hwin onePending twoPending hselected
                ((env n).inputOne, (env n).inputTwo)
          have hpairNext :
              ((.inl oneNext : OneControl A strategy hwin package),
                (.inl twoNext : TwoControl A strategy hwin package)) =
                package.literalCombinedFreshPhaseLiveRootSemanticTrace A
                  strategy hwin env (n + 1) := by
            have hnextCanonical :=
              (package.literalCombinedFreshPhaseLiveRootSelectedTraceLaws A
                strategy hwin env).both n (.inl onePending)
                  (.inl twoPending) trivial hcanonicalSelected hgraph |>.1
            rcases hnextCanonical with ⟨_, _, _, _, _, htraceNext⟩
            exact htraceNext
          exact ⟨oneNext, twoNext,
            (congrArg Prod.fst hpairNext).symm,
            (congrArg Prod.snd hpairNext).symm, hnext, rfl⟩

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
