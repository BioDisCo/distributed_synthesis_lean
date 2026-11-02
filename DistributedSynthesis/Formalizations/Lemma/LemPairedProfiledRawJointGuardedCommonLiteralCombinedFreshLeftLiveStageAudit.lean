/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshReceiveOneHandler
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralExactMirrorTaggedStagedFront

/-!
# Live left-stage audit for the combined pending handler

This is a deliberately isolated fail-fast comparison.  Start with the same
pending member on both endpoints, regard process one's stored left sender and
process two's selected left receiver as a live staged pair, and reverse to a
strict-left round.  The established staged theorem activates a recurrent
matched-left pair from the receiver's latest `some stage`.

The current combined pending maps do something different: process one's
receive reads its *own right* receiver fork, process two's nonreceive advances
its *own right* sender, and both postcontrols remain in the pending (`Sum.inl`)
phase.  The theorem below records the strongest definitional output equations,
reuses `literalLeftSeamStagedReversal_exact_pair` for the intended outputs and
postcontrols, and proves that the two combined postcontrols cannot equal the
embedded recurrent postcontrols.  This is a structural constructor mismatch,
not a failed automation attempt or a special finite instance.
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

private abbrev OneShared (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralCombinedFreshOneShared A strategy hwin
    package

private abbrev TwoShared (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoShared A strategy hwin
    package

private abbrev OnePayload (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralCombinedFreshOnePayload A strategy hwin
    package

private abbrev TwoPayload (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoPayload A strategy hwin
    package

private abbrev LeftOne (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralLeftSeamOneControl A strategy hwin
    package

private abbrev LeftTwo (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralLeftSeamTwoControl A strategy hwin
    package

private abbrev CombinedOne (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralCombinedFreshOneControl A strategy hwin
    package (LeftOne A strategy hwin package)

private abbrev CombinedTwo (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoControl A strategy hwin
    package (LeftTwo A strategy hwin package)

private abbrev LeftStage (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralLeftSeamStage A strategy hwin package

/-! ## Exact audit -/

/-- On a live left staged pair, the current combined pending maps cannot be
the reversal maps.  Besides the constructor inequalities, the first two
conjuncts name the actual output sources chosen by the combined maps, while
the third conjunct is the established exact recurrent-pair equation. -/
theorem literalCombinedFresh_left_live_stage_reversal_audit
    (package : Package A strategy hwin initial)
    (member : Bool)
    (oneShared : OneShared A strategy hwin package)
    (twoShared : TwoShared A strategy hwin package)
    (onePayload : OnePayload A strategy hwin package)
    (twoPayload : TwoPayload A strategy hwin package)
    (stage : LeftStage A strategy hwin package)
    (hstage :
      (package.literalCombinedFreshTwoReceiver A strategy hwin member
        twoShared).2.2.2 = some stage)
    (input : In₁ × In₂)
    (recurrentRecv :
      ProfiledRawJointGuardedCommonLiteralCombinedFreshRecurrentRecvForkOne A
        strategy hwin package (LeftOne A strategy hwin package)
          (LeftTwo A strategy hwin package))
    (mixedRecv :
      ProfiledRawJointGuardedCommonLiteralCombinedFreshMixedRecvForkOne A
        strategy hwin package (LeftOne A strategy hwin package)
          (LeftTwo A strategy hwin package))
    (recurrentNoRecvTwo :
      LeftTwo A strategy hwin package → In₂ →
        LeftTwo A strategy hwin package × Out₂) :
    let onePending :=
      (member, oneShared, onePayload)
    let twoPending :=
      (member, twoShared, twoPayload)
    let combinedOne := package.literalCombinedFreshOpenRecvOne A strategy hwin
      (LeftOne A strategy hwin package) (LeftTwo A strategy hwin package)
      recurrentRecv mixedRecv (.inl onePending) input.1 (.inl twoPending)
        input.2
    let combinedTwo :=
      FiniteAcknowledgedDelayedCarrier.deferredOrRecurrentNoRecv
        (package.literalCombinedFreshTwoPendingStep A strategy hwin)
        recurrentNoRecvTwo (.inl twoPending) input.2
    let receiver := package.literalCombinedFreshTwoReceiver A strategy hwin
      member twoShared
    let exactOne := package.literalLeftSeamStagedReversalRecvOne A strategy
      hwin oneShared.2.1 input.1 receiver input.2
    let exactTwo := package.literalLeftSeamStagedReversalNoRecvTwo A strategy
      hwin receiver input.2
    combinedOne.2 =
        package.literalCombinedFreshOneSelectedPhysicalOutput A strategy hwin
          member
          (package.literalRightSeamStagedReceiverRecv A strategy hwin
            (package.literalCombinedFreshOneReceiver A strategy hwin member
              oneShared) input.1 input.2).1 ∧
      combinedTwo.2 =
        (package.literalRightSeamStagedSenderNoRecv A strategy hwin
          twoShared.2.1 input.2).1 ∧
      (let matched := package.literalLeftSeamStageMatched A strategy hwin stage
       exactOne =
          ((package.literalLeftSeamTaggedRecvOne A strategy hwin matched.1
            input.1 matched.2 input.2).2,
            (package.literalLeftSeamTaggedRecvOne A strategy hwin matched.1
              input.1 matched.2 input.2).1) ∧
        exactTwo =
          ((package.literalLeftSeamTaggedNoRecvTwo A strategy hwin matched.2
            input.2).2,
            (package.literalLeftSeamTaggedNoRecvTwo A strategy hwin matched.2
              input.2).1)) ∧
      combinedOne.1 ≠
        (.inr exactOne.2 : CombinedOne A strategy hwin package) ∧
      combinedTwo.1 ≠
        (.inr exactTwo.2 : CombinedTwo A strategy hwin package) := by
  dsimp only
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · exact package.literalLeftSeamStagedReversal_exact_pair A strategy hwin
      (package.literalCombinedFreshTwoReceiver A strategy hwin member
        twoShared) oneShared.2.1 stage hstage input
  constructor
  · intro h
    change Sum.inl _ = Sum.inr _ at h
    cases h
  · simp [FiniteAcknowledgedDelayedCarrier.deferredOrRecurrentNoRecv]

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
