/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshPhaseActivatedPendingBridge
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralBranchStagePhysicalPriority

/-!
# Hard-cut invariant of the physical phase-live table

The activated controller is used only as a proof-side liveness classifier.
The actual finite machine remains the phase-live table controller.  This file
collects the two pieces of information available at every physical trace
point: root reachability and the exact input segment represented by the same
pending controls.  It then exposes receiver-only reachability of the table
that is physically live in either strict direction.

The parity-facing target is always read at entry row `.both` directly from
the selected table member.  It is intentionally not identified with the row
stored in the optional retained stage: that row can be `.first` on a reachable
false member.  All choices and orientation cases here are proof-side only.
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

/-! ## One common pending trace witness -/

/-- Root reachability and exact segment bookkeeping refer to the same
canonical pending controls at every time. -/
theorem literalCombinedFreshPhaseLiveSemanticTrace_rootReachable_segment
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    ∃ one : OnePending A strategy hwin package,
      ∃ two : TwoPending A strategy hwin package,
        package.literalCombinedFreshPhaseLiveRootSemanticTrace A strategy hwin
            env n = (.inl one, .inl two) ∧
          package.LiteralCombinedFreshPhaseLiveRootReachableSelected A strategy
              hwin one two ∧
            package.LiteralCombinedFreshPhaseLiveRootSegmentSelected A
              strategy hwin env n one two := by
  have hsegment :=
    package.literalCombinedFreshPhaseLiveRootSemanticTrace_tableSegment A
      strategy hwin env n
  rcases hsegment with
    ⟨one, two, hone, htwo, hsegmentSelected, _hsegmentTrace⟩
  have htrace :
      package.literalCombinedFreshPhaseLiveRootSemanticTrace A strategy hwin
        env n = (.inl one, .inl two) := by
    apply Prod.ext
    · exact hone
    · exact htwo
  have hroot :=
    package.literalCombinedFreshPhaseLiveRootSemanticTrace_rootReachable A
      strategy hwin env n
  rw [htrace] at hroot
  rcases hroot with
    ⟨rootOne, rootTwo, hrootOne, hrootTwo, hrootSelected, _hrootTrace⟩
  have honeEq := Sum.inl.inj hrootOne
  have htwoEq := Sum.inl.inj hrootTwo
  subst rootOne
  subst rootTwo
  exact ⟨one, two, htrace, hrootSelected, hsegmentSelected⟩

/-! ## Receiver-only local reachability in both orientations -/

/-- Forget the synchronized sender from a left root-prefix witness while
retaining an existential proof-side sender at the same prefix. -/
theorem literalLeftSeamReceiverTableLocallyReachable_of_rootReachable
    (package : Package A strategy hwin (initial := initial))
    (receiver : LeftReceiver A strategy hwin package)
    (sender : LeftSender A strategy hwin package)
    (hreach : package.LiteralLeftSeamTableRootReachable A strategy hwin
      receiver sender) :
    package.LiteralLeftSeamReceiverTableLocallyReachable A strategy hwin
      receiver := by
  rcases hreach with ⟨past, _hsender, hreceiver⟩
  let table :=
    profiledRawJointLiteralLeftBothExactHeterogeneousRightTable A strategy hwin
      (package.literalLeftSeamInstalled A strategy hwin receiver.1)
  refine ⟨finiteCrossAnchorSenderAtPrefix table past, past, rfl, ?_⟩
  exact hreceiver

/-- The right receiver selected by an honest phase-live strict-left receive
is locally reachable in its internally selected table member. -/
theorem literalCombinedFreshLiveRightReceiverForRecvOne_locallyReachable
    (package : Package A strategy hwin (initial := initial))
    (one : OnePending A strategy hwin package)
    (two : TwoPending A strategy hwin package)
    (hselected :
      package.LiteralCombinedFreshPhaseLiveRootReachableSelected A strategy
        hwin one two) :
    package.LiteralRightSeamReceiverTableLocallyReachable A strategy hwin
      (package.literalCombinedFreshLiveRightReceiverForRecvOne A strategy hwin
        one two) := by
  cases hone : one.2.1.1.2 <;> cases htwo : two.2.1.1.2
  · rw [package.literalCombinedFreshLiveRightReceiverForRecvOne_switch A
      strategy hwin one two hone]
    exact package.literalRightSeamReceiverTableLocallyReachable_initial A
      strategy hwin _ _ _
  · rw [package.literalCombinedFreshLiveRightReceiverForRecvOne_switch A
      strategy hwin one two hone]
    exact package.literalRightSeamReceiverTableLocallyReachable_initial A
      strategy hwin _ _ _
  · rw [package.literalCombinedFreshLiveRightReceiverForRecvOne_same A
      strategy hwin one two hone]
    simp only [LiteralCombinedFreshPhaseLiveRootReachableSelected,
      LiteralCombinedFreshPhaseLiveTableRootReachable, hone, htwo] at hselected
    exact package.literalRightSeamReceiverTableLocallyReachable_of_rootReachable
      A strategy hwin _ _ hselected.2.1
  · rw [package.literalCombinedFreshLiveRightReceiverForRecvOne_same A
      strategy hwin one two hone]
    simp only [LiteralCombinedFreshPhaseLiveRootReachableSelected,
      LiteralCombinedFreshPhaseLiveTableRootReachable, hone, htwo] at hselected
    exact package.literalRightSeamReceiverTableLocallyReachable_of_rootReachable
      A strategy hwin _ _ hselected.2

/-- Mirror receiver-only reachability for an honest strict-right receive. -/
theorem literalCombinedFreshLiveLeftReceiverForRecvTwo_locallyReachable
    (package : Package A strategy hwin (initial := initial))
    (two : TwoPending A strategy hwin package)
    (one : OnePending A strategy hwin package)
    (hselected :
      package.LiteralCombinedFreshPhaseLiveRootReachableSelected A strategy
        hwin one two) :
    package.LiteralLeftSeamReceiverTableLocallyReachable A strategy hwin
      (package.literalCombinedFreshLiveLeftReceiverForRecvTwo A strategy hwin
        two one) := by
  cases hone : one.2.1.1.2 <;> cases htwo : two.2.1.1.2
  · rw [package.literalCombinedFreshLiveLeftReceiverForRecvTwo_same A strategy
      hwin two one htwo]
    simp only [LiteralCombinedFreshPhaseLiveRootReachableSelected,
      LiteralCombinedFreshPhaseLiveTableRootReachable, hone, htwo] at hselected
    exact package.literalLeftSeamReceiverTableLocallyReachable_of_rootReachable
      A strategy hwin _ _ hselected.2
  · rw [package.literalCombinedFreshLiveLeftReceiverForRecvTwo_switch A
      strategy hwin two one htwo]
    apply package.literalLeftSeamReceiverTableLocallyReachable_of_rootReachable
      A strategy hwin
    exact package.literalLeftSeamTableRootReachable_initial A strategy hwin _ _
      _
  · rw [package.literalCombinedFreshLiveLeftReceiverForRecvTwo_same A strategy
      hwin two one htwo]
    simp only [LiteralCombinedFreshPhaseLiveRootReachableSelected,
      LiteralCombinedFreshPhaseLiveTableRootReachable, hone, htwo] at hselected
    exact package.literalLeftSeamReceiverTableLocallyReachable_of_rootReachable
      A strategy hwin _ _ hselected.2.2
  · rw [package.literalCombinedFreshLiveLeftReceiverForRecvTwo_switch A
      strategy hwin two one htwo]
    apply package.literalLeftSeamReceiverTableLocallyReachable_of_rootReachable
      A strategy hwin
    exact package.literalLeftSeamTableRootReachable_initial A strategy hwin _ _
      _

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
