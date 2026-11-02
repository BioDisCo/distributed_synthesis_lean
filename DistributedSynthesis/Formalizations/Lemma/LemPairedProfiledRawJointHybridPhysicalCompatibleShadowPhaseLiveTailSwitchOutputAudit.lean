/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointCrossReceiverPhysicalProjection
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailTrackedInvariant

/-!
# The exact output law at a tagged-tail direction switch

The phase-live state already contains the two locally meaningful receive
calculations.  On a receive, process one must use the left-table receiver and
process two must use the right-table receiver: these are the projections that
are indistinguishable from strict-left and strict-right, respectively.

Their simultaneous use is sound precisely when the two resulting records
satisfy the ordinary cross-receiver anti-mosaic equations.  This file names
that law and proves that it is exactly sufficient to view the local output
pair as the checked close of either orientation.  It does not claim that the
current tracked invariant implies the law; that is the fail-fast model test.
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

private abbrev Tag :=
  ProfiledRawJointHybridShadowPhaseLiveTag A strategy hwin

private abbrev OnePending (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailOnePending A strategy hwin tag

private abbrev TwoPending (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailTwoPending A strategy hwin tag

private abbrev RightOutput (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailRightReceiverOutput A strategy hwin
    tag

private abbrev LeftOutput (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailLeftReceiverOutput A strategy hwin
    tag

/-! ## The two locally forced receive records -/

noncomputable def profiledRawJointHybridShadowPhaseLiveTailSwitchRightRecord
    (tag : Tag A strategy hwin) (fallback : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂) :
    RightOutput A strategy hwin tag :=
  profiledRawJointHybridShadowPhaseLiveTailRightSingleTableRecord A strategy
    hwin tag fallback one.2.1.baseShared
      (profiledRawJointHybridShadowPhaseLiveTailRightReceiverForRecvTwo A
        strategy hwin tag two one) (input.2, input.1)

noncomputable def profiledRawJointHybridShadowPhaseLiveTailSwitchLeftRecord
    (tag : Tag A strategy hwin) (fallback : LeftOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂) :
    LeftOutput A strategy hwin tag :=
  profiledRawJointHybridShadowPhaseLiveTailLeftSingleTableRecord A strategy
    hwin tag fallback two.2.1.baseShared
      (profiledRawJointHybridShadowPhaseLiveTailLeftReceiverForRecvOne A
        strategy hwin tag one two) input

/-- The two cross equations needed when both endpoints execute their locally
forced receive projection.  This is proof data, not a runtime test. -/
def ProfiledRawJointHybridShadowPhaseLiveTailSwitchOutputCompatible
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂) : Prop :=
  let right :=
    profiledRawJointHybridShadowPhaseLiveTailSwitchRightRecord A strategy hwin
      tag fallbackRight one two input
  let left :=
    profiledRawJointHybridShadowPhaseLiveTailSwitchLeftRecord A strategy hwin
      tag fallbackLeft one two input
  right.physical.closingBoth = pairedLeftInformedForRow .both left.physical ∧
    left.physical.closingBoth = pairedRightInformedForRow .both right.physical

/-- The actual receive-side projections: process one reads the left record and
process two reads the right record.  Neither function receives a graph or a
leader/orientation bit. -/
noncomputable def profiledRawJointHybridShadowPhaseLiveTailSwitchOutputOne
    (tag : Tag A strategy hwin) (fallback : LeftOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂) : Out₁ :=
  pairedLeftInformedForRow .both
    (profiledRawJointHybridShadowPhaseLiveTailSwitchLeftRecord A strategy hwin
      tag fallback one two input).physical

noncomputable def profiledRawJointHybridShadowPhaseLiveTailSwitchOutputTwo
    (tag : Tag A strategy hwin) (fallback : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂) : Out₂ :=
  pairedRightInformedForRow .both
    (profiledRawJointHybridShadowPhaseLiveTailSwitchRightRecord A strategy hwin
      tag fallback one two input).physical

/-! ## Exact sufficiency of the anti-mosaic law -/

theorem
    ProfiledRawJointHybridShadowPhaseLiveTailSwitchOutputCompatible.outputs_eq_closings
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂)
    (hcompatible :
      ProfiledRawJointHybridShadowPhaseLiveTailSwitchOutputCompatible A
        strategy hwin tag fallbackLeft fallbackRight one two input) :
    let right :=
      profiledRawJointHybridShadowPhaseLiveTailSwitchRightRecord A strategy hwin
        tag fallbackRight one two input
    let left :=
      profiledRawJointHybridShadowPhaseLiveTailSwitchLeftRecord A strategy hwin
        tag fallbackLeft one two input
    let output :=
      (profiledRawJointHybridShadowPhaseLiveTailSwitchOutputOne A strategy hwin
          tag fallbackLeft one two input,
        profiledRawJointHybridShadowPhaseLiveTailSwitchOutputTwo A strategy hwin
          tag fallbackRight one two input)
    output = (pairedRightClosingForRow .both right.physical,
        pairedRightInformedForRow .both right.physical) ∧
      output = (pairedLeftInformedForRow .both left.physical,
        pairedLeftClosingForRow .both left.physical) := by
  dsimp only
  rcases hcompatible with ⟨hone, htwo⟩
  constructor
  · exact Prod.ext hone.symm rfl
  · exact Prod.ext rfl htwo.symm

end

end DetParityAutomaton

end DistributedSynthesis
