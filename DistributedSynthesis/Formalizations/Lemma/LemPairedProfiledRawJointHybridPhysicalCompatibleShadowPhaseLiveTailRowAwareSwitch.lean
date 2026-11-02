/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailSwitchOutputCouplingPreservationAudit
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleLiteralPrefixCurrentCrossPacket

/-!
# Row-aware cross laws at recurrent Tail switches

The older Tail audit projected `.both` from both receiver records after every
constructor.  That is correct for a closed simultaneous successor, but not
for a freshly opened receiver after a strict switch: the open member is the
fresh `.first` row.  The retained receiver, moreover, keeps its own entry row.

This file states the constructor laws at the rows actually stored in the two
local receiver controls.  It changes no executable state and supplies no
graph, orientation, leader, or strict-leader input to a process.
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

/-! ## Rows selected by the actual local receiver controls -/

def profiledRawJointHybridShadowPhaseLiveTailSwitchRightRow
    (tag : Tag A strategy hwin) (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) : PairedEntryRow :=
  profiledRawJointHybridShadowPhaseLiveTailRightReceiverRow A strategy hwin tag
    (profiledRawJointHybridShadowPhaseLiveTailRightReceiverForRecvTwo A
      strategy hwin tag two one)

def profiledRawJointHybridShadowPhaseLiveTailSwitchLeftRow
    (tag : Tag A strategy hwin) (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) : PairedEntryRow :=
  profiledRawJointHybridShadowPhaseLiveTailLeftReceiverRow A strategy hwin tag
    (profiledRawJointHybridShadowPhaseLiveTailLeftReceiverForRecvOne A strategy
      hwin tag one two)

/-! ## Correct state-local and constructor-local laws -/

/-- The phase-selected anti-mosaic equation, evaluated at the rows actually
stored in the two receiver controls. -/
def ProfiledRawJointHybridShadowPhaseLiveTailRowSwitchOutputCompatible
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
  let rightRow :=
    profiledRawJointHybridShadowPhaseLiveTailSwitchRightRow A strategy hwin tag
      one two
  let leftRow :=
    profiledRawJointHybridShadowPhaseLiveTailSwitchLeftRow A strategy hwin tag
      one two
  if one.2.1.localPhase then
    pairedLeftClosingForRow leftRow left.physical =
      pairedRightInformedForRow rightRow right.physical
  else
    pairedRightClosingForRow rightRow right.physical =
      pairedLeftInformedForRow leftRow left.physical

def ProfiledRawJointHybridShadowPhaseLiveTailRowSwitchCoupled
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) : Prop :=
  ∀ input : In₁ × In₂,
    ProfiledRawJointHybridShadowPhaseLiveTailRowSwitchOutputCompatible A
      strategy hwin tag fallbackLeft fallbackRight one two input

/-- Correct strict-right constructor field: retained-right closing at its
stored row equals fresh-left informed output at its stored (open) row. -/
def ProfiledRawJointHybridShadowPhaseLiveTailRowStrictRightConstructorCross
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂) : Prop :=
  let next :=
    profiledRawJointHybridShadowPhaseLiveTailSwitchStrictRightNext A strategy
      hwin tag fallbackLeft fallbackRight one two input
  ∀ nextInput : In₁ × In₂,
    let right :=
      profiledRawJointHybridShadowPhaseLiveTailSwitchRightRecord A strategy hwin
        tag fallbackRight next.1 next.2 nextInput
    let left :=
      profiledRawJointHybridShadowPhaseLiveTailSwitchLeftRecord A strategy hwin
        tag fallbackLeft next.1 next.2 nextInput
    pairedRightClosingForRow
        (profiledRawJointHybridShadowPhaseLiveTailSwitchRightRow A strategy hwin
          tag next.1 next.2) right.physical =
      pairedLeftInformedForRow
        (profiledRawJointHybridShadowPhaseLiveTailSwitchLeftRow A strategy hwin
          tag next.1 next.2) left.physical

/-- Strict-left mirror. -/
def ProfiledRawJointHybridShadowPhaseLiveTailRowStrictLeftConstructorCross
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂) : Prop :=
  let next :=
    profiledRawJointHybridShadowPhaseLiveTailSwitchStrictLeftNext A strategy
      hwin tag fallbackLeft fallbackRight one two input
  ∀ nextInput : In₁ × In₂,
    let right :=
      profiledRawJointHybridShadowPhaseLiveTailSwitchRightRecord A strategy hwin
        tag fallbackRight next.1 next.2 nextInput
    let left :=
      profiledRawJointHybridShadowPhaseLiveTailSwitchLeftRecord A strategy hwin
        tag fallbackLeft next.1 next.2 nextInput
    pairedLeftClosingForRow
        (profiledRawJointHybridShadowPhaseLiveTailSwitchLeftRow A strategy hwin
          tag next.1 next.2) left.physical =
      pairedRightInformedForRow
        (profiledRawJointHybridShadowPhaseLiveTailSwitchRightRow A strategy hwin
          tag next.1 next.2) right.physical

/-- Simultaneous-close field in row-aware form.  The timing lemmas identify
both rows with `.both` for this constructor. -/
def ProfiledRawJointHybridShadowPhaseLiveTailRowBothConstructorCross
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂) : Prop :=
  let next :=
    profiledRawJointHybridShadowPhaseLiveTailSwitchBothNext A strategy hwin tag
      fallbackLeft fallbackRight one two input
  ∀ nextInput : In₁ × In₂,
    let right :=
      profiledRawJointHybridShadowPhaseLiveTailSwitchRightRecord A strategy hwin
        tag fallbackRight next.1 next.2 nextInput
    let left :=
      profiledRawJointHybridShadowPhaseLiveTailSwitchLeftRecord A strategy hwin
        tag fallbackLeft next.1 next.2 nextInput
    pairedLeftClosingForRow
        (profiledRawJointHybridShadowPhaseLiveTailSwitchLeftRow A strategy hwin
          tag next.1 next.2) left.physical =
      pairedRightInformedForRow
        (profiledRawJointHybridShadowPhaseLiveTailSwitchRightRow A strategy hwin
          tag next.1 next.2) right.physical

/-! ## Exact one-step preservation -/

theorem profiledRawJointHybridShadowPhaseLiveTailStrictRight_next_rowCoupled_iff
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂) :
    let next :=
      profiledRawJointHybridShadowPhaseLiveTailSwitchStrictRightNext A strategy
        hwin tag fallbackLeft fallbackRight one two input
    ProfiledRawJointHybridShadowPhaseLiveTailRowSwitchCoupled A strategy hwin
        tag fallbackLeft fallbackRight next.1 next.2 ↔
      ProfiledRawJointHybridShadowPhaseLiveTailRowStrictRightConstructorCross A
        strategy hwin tag fallbackLeft fallbackRight one two input := by
  dsimp only
  constructor <;> intro h nextInput
  · simpa [ProfiledRawJointHybridShadowPhaseLiveTailRowSwitchCoupled,
      ProfiledRawJointHybridShadowPhaseLiveTailRowSwitchOutputCompatible,
      profiledRawJointHybridShadowPhaseLiveTailSwitchStrictRightNext] using
      h nextInput
  · simpa [ProfiledRawJointHybridShadowPhaseLiveTailRowSwitchCoupled,
      ProfiledRawJointHybridShadowPhaseLiveTailRowSwitchOutputCompatible,
      profiledRawJointHybridShadowPhaseLiveTailSwitchStrictRightNext] using
      h nextInput

theorem profiledRawJointHybridShadowPhaseLiveTailStrictLeft_next_rowCoupled_iff
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂) :
    let next :=
      profiledRawJointHybridShadowPhaseLiveTailSwitchStrictLeftNext A strategy
        hwin tag fallbackLeft fallbackRight one two input
    ProfiledRawJointHybridShadowPhaseLiveTailRowSwitchCoupled A strategy hwin
        tag fallbackLeft fallbackRight next.1 next.2 ↔
      ProfiledRawJointHybridShadowPhaseLiveTailRowStrictLeftConstructorCross A
        strategy hwin tag fallbackLeft fallbackRight one two input := by
  dsimp only
  constructor <;> intro h nextInput
  · simpa [ProfiledRawJointHybridShadowPhaseLiveTailRowSwitchCoupled,
      ProfiledRawJointHybridShadowPhaseLiveTailRowSwitchOutputCompatible,
      profiledRawJointHybridShadowPhaseLiveTailSwitchStrictLeftNext] using
      h nextInput
  · simpa [ProfiledRawJointHybridShadowPhaseLiveTailRowSwitchCoupled,
      ProfiledRawJointHybridShadowPhaseLiveTailRowSwitchOutputCompatible,
      profiledRawJointHybridShadowPhaseLiveTailSwitchStrictLeftNext] using
      h nextInput

theorem profiledRawJointHybridShadowPhaseLiveTailBoth_next_rowCoupled_iff
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂) :
    let next :=
      profiledRawJointHybridShadowPhaseLiveTailSwitchBothNext A strategy hwin
        tag fallbackLeft fallbackRight one two input
    ProfiledRawJointHybridShadowPhaseLiveTailRowSwitchCoupled A strategy hwin
        tag fallbackLeft fallbackRight next.1 next.2 ↔
      ProfiledRawJointHybridShadowPhaseLiveTailRowBothConstructorCross A
        strategy hwin tag fallbackLeft fallbackRight one two input := by
  dsimp only
  constructor <;> intro h nextInput
  · simpa [ProfiledRawJointHybridShadowPhaseLiveTailRowSwitchCoupled,
      ProfiledRawJointHybridShadowPhaseLiveTailRowSwitchOutputCompatible,
      profiledRawJointHybridShadowPhaseLiveTailSwitchBothNext] using h nextInput
  · simpa [ProfiledRawJointHybridShadowPhaseLiveTailRowSwitchCoupled,
      ProfiledRawJointHybridShadowPhaseLiveTailRowSwitchOutputCompatible,
      profiledRawJointHybridShadowPhaseLiveTailSwitchBothNext] using h nextInput

end


end DetParityAutomaton

end DistributedSynthesis
