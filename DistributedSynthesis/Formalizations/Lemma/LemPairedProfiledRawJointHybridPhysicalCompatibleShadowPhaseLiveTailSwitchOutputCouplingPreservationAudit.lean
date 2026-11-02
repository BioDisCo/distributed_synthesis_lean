/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailSwitchOutputTrackedBoundary

/-!
# One-step preservation audit for the phase-indexed switch law

The weakest output coupling needed at one pending state is the single cross
equation selected by process one's public phase.  This file quantifies that
law over the next complete input and tests it against the three concrete
`TailFreshPair` successors.

The result is exact.  The concrete constructors force the successor phases:

* strict right produces `(false, false)` and needs the right-closing/left-live
  equation;
* strict left produces `(true, true)` and needs the left-closing/right-live
  equation;
* simultaneous close produces `(true, false)` and needs that same left-selected
  equation.

Those three equations are not fields of `TailTrackedInvariant` or of the
fresh pending payload.  The payload stores target keys and separately tracked
receivers, but no same-occurrence cross-output witness.  The theorems below
show that adding exactly the named constructor equation is equivalent to
one-step preservation; no full guarded-root pinning is assumed.
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

/-! ## The weakest state-local law -/

/-- The one phase-selected cross equation holds for every possible next
complete input.  This is strictly weaker than full two-equation compatibility
and contains no semantic representative or root pin. -/
def ProfiledRawJointHybridShadowPhaseLiveTailPhaseSwitchCoupled
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) : Prop :=
  ∀ input : In₁ × In₂,
    ProfiledRawJointHybridShadowPhaseLiveTailPhaseSwitchOutputCompatible A
      strategy hwin tag fallbackLeft fallbackRight one two input

theorem
    ProfiledRawJointHybridShadowPhaseLiveTailPhaseSwitchCoupled.output_eq_freshPair
    {tag : Tag A strategy hwin} {fallbackLeft : LeftOutput A strategy hwin tag}
    {fallbackRight : RightOutput A strategy hwin tag}
    {one : OnePending A strategy hwin tag}
    {two : TwoPending A strategy hwin tag}
    (hcoupled :
      ProfiledRawJointHybridShadowPhaseLiveTailPhaseSwitchCoupled A strategy
        hwin tag fallbackLeft fallbackRight one two)
    (hinvariant :
      ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant A strategy hwin
        tag one two)
    (input : In₁ × In₂) :
    (profiledRawJointHybridShadowPhaseLiveTailSwitchOutputOne A strategy hwin
        tag fallbackLeft one two input,
      profiledRawJointHybridShadowPhaseLiveTailSwitchOutputTwo A strategy hwin
        tag fallbackRight one two input) =
      (profiledRawJointHybridShadowPhaseLiveTailFreshPair A strategy hwin tag
        fallbackLeft fallbackRight one two input).2 :=
  (hcoupled input).output_eq_freshPair A strategy hwin tag fallbackLeft
    fallbackRight one two input hinvariant

/-! ## The three concrete successors -/

noncomputable def
    profiledRawJointHybridShadowPhaseLiveTailSwitchStrictRightNext
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂) :
    OnePending A strategy hwin tag × TwoPending A strategy hwin tag :=
  let oneNext :=
    (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
      (profiledRawJointHybridShadowPhaseLiveTailOnePendingStep A strategy hwin
        tag) one input.1).1
  let fresh :=
    profiledRawJointHybridShadowPhaseLiveTailFreshPair.{u, v, x, y, s,
      max u v x y s, max u v x y s, max u v x y s,
      max u v x y s, max u v x y s, max u v x y s,
      max u v x y s, max u v x y s} A strategy hwin tag fallbackLeft
        fallbackRight one two input
  (oneNext, fresh.1.2.openControl)

noncomputable def
    profiledRawJointHybridShadowPhaseLiveTailSwitchStrictLeftNext
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂) :
    OnePending A strategy hwin tag × TwoPending A strategy hwin tag :=
  let fresh :=
    profiledRawJointHybridShadowPhaseLiveTailFreshPair.{u, v, x, y, s,
      max u v x y s, max u v x y s, max u v x y s,
      max u v x y s, max u v x y s, max u v x y s,
      max u v x y s, max u v x y s} A strategy hwin tag fallbackLeft
        fallbackRight one two input
  let twoNext :=
    (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
      (profiledRawJointHybridShadowPhaseLiveTailTwoPendingStep A strategy hwin
        tag) two input.2).1
  (fresh.1.1.openControl, twoNext)

noncomputable def
    profiledRawJointHybridShadowPhaseLiveTailSwitchBothNext
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂) :
    OnePending A strategy hwin tag × TwoPending A strategy hwin tag :=
  let fresh :=
    profiledRawJointHybridShadowPhaseLiveTailFreshPair.{u, v, x, y, s,
      max u v x y s, max u v x y s, max u v x y s,
      max u v x y s, max u v x y s, max u v x y s,
      max u v x y s, max u v x y s} A strategy hwin tag fallbackLeft
        fallbackRight one two input
  (fresh.1.1.closedControl, fresh.1.2.closedControl)

@[simp] theorem
    profiledRawJointHybridShadowPhaseLiveTailSwitchStrictRightNext_phases
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂) :
    let next :=
      profiledRawJointHybridShadowPhaseLiveTailSwitchStrictRightNext A strategy
        hwin tag fallbackLeft fallbackRight one two input
    next.1.2.1.localPhase = false ∧
      next.2.2.1.localPhase = false := by
  simp [profiledRawJointHybridShadowPhaseLiveTailSwitchStrictRightNext,
    profiledRawJointHybridShadowPhaseLiveTailOnePendingStep,
    FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv,
    FiniteAcknowledgedDelayedCarrier.phaseLivePendingStep,
    FiniteAcknowledgedDelayedCarrier.PhaseLiveShared.fresh,
    profiledRawJointHybridShadowPhaseLiveTailFreshPair]

@[simp] theorem
    profiledRawJointHybridShadowPhaseLiveTailSwitchStrictLeftNext_phases
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂) :
    let next :=
      profiledRawJointHybridShadowPhaseLiveTailSwitchStrictLeftNext A strategy
        hwin tag fallbackLeft fallbackRight one two input
    next.1.2.1.localPhase = true ∧
      next.2.2.1.localPhase = true := by
  simp [profiledRawJointHybridShadowPhaseLiveTailSwitchStrictLeftNext,
    profiledRawJointHybridShadowPhaseLiveTailTwoPendingStep,
    FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv,
    FiniteAcknowledgedDelayedCarrier.phaseLivePendingStep,
    FiniteAcknowledgedDelayedCarrier.PhaseLiveShared.fresh,
    profiledRawJointHybridShadowPhaseLiveTailFreshPair]

@[simp] theorem
    profiledRawJointHybridShadowPhaseLiveTailSwitchBothNext_phases
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂) :
    let next :=
      profiledRawJointHybridShadowPhaseLiveTailSwitchBothNext A strategy hwin
        tag fallbackLeft fallbackRight one two input
    next.1.2.1.localPhase = true ∧
      next.2.2.1.localPhase = false := by
  simp [profiledRawJointHybridShadowPhaseLiveTailSwitchBothNext,
    profiledRawJointHybridShadowPhaseLiveTailFreshPair,
    FiniteAcknowledgedDelayedCarrier.PhaseLiveShared.fresh]

/-! ## Exact constructor fields -/

/-- The field absent from a strict-right fresh constructor: at every following
input, the continued right record's closing process-one coordinate must equal
the freshly installed left receiver's process-one coordinate. -/
def ProfiledRawJointHybridShadowPhaseLiveTailStrictRightConstructorCross
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
    right.physical.closingBoth =
      pairedLeftInformedForRow .both left.physical

/-- Strict-left mirror constructor field. -/
def ProfiledRawJointHybridShadowPhaseLiveTailStrictLeftConstructorCross
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
    left.physical.closingBoth =
      pairedRightInformedForRow .both right.physical

/-- Simultaneous-close constructor field.  Its canonical `(true,false)` phase
also selects the left-record equation. -/
def ProfiledRawJointHybridShadowPhaseLiveTailBothConstructorCross
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
    left.physical.closingBoth =
      pairedRightInformedForRow .both right.physical

/-! ## Preservation is equivalent to exactly those fields -/

theorem
    profiledRawJointHybridShadowPhaseLiveTailStrictRight_next_coupled_iff
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂) :
    let next :=
      profiledRawJointHybridShadowPhaseLiveTailSwitchStrictRightNext A strategy
        hwin tag fallbackLeft fallbackRight one two input
    ProfiledRawJointHybridShadowPhaseLiveTailPhaseSwitchCoupled A strategy hwin
        tag fallbackLeft fallbackRight next.1 next.2 ↔
      ProfiledRawJointHybridShadowPhaseLiveTailStrictRightConstructorCross A
        strategy hwin tag fallbackLeft fallbackRight one two input := by
  dsimp only
  constructor <;> intro h nextInput
  · simpa [ProfiledRawJointHybridShadowPhaseLiveTailPhaseSwitchCoupled,
      ProfiledRawJointHybridShadowPhaseLiveTailPhaseSwitchOutputCompatible,
      profiledRawJointHybridShadowPhaseLiveTailSwitchStrictRightNext] using
        h nextInput
  · simpa [ProfiledRawJointHybridShadowPhaseLiveTailPhaseSwitchCoupled,
      ProfiledRawJointHybridShadowPhaseLiveTailPhaseSwitchOutputCompatible,
      profiledRawJointHybridShadowPhaseLiveTailSwitchStrictRightNext] using
        h nextInput

theorem
    profiledRawJointHybridShadowPhaseLiveTailStrictLeft_next_coupled_iff
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂) :
    let next :=
      profiledRawJointHybridShadowPhaseLiveTailSwitchStrictLeftNext A strategy
        hwin tag fallbackLeft fallbackRight one two input
    ProfiledRawJointHybridShadowPhaseLiveTailPhaseSwitchCoupled A strategy hwin
        tag fallbackLeft fallbackRight next.1 next.2 ↔
      ProfiledRawJointHybridShadowPhaseLiveTailStrictLeftConstructorCross A
        strategy hwin tag fallbackLeft fallbackRight one two input := by
  dsimp only
  constructor <;> intro h nextInput
  · simpa [ProfiledRawJointHybridShadowPhaseLiveTailPhaseSwitchCoupled,
      ProfiledRawJointHybridShadowPhaseLiveTailPhaseSwitchOutputCompatible,
      profiledRawJointHybridShadowPhaseLiveTailSwitchStrictLeftNext] using
        h nextInput
  · simpa [ProfiledRawJointHybridShadowPhaseLiveTailPhaseSwitchCoupled,
      ProfiledRawJointHybridShadowPhaseLiveTailPhaseSwitchOutputCompatible,
      profiledRawJointHybridShadowPhaseLiveTailSwitchStrictLeftNext] using
        h nextInput

theorem profiledRawJointHybridShadowPhaseLiveTailBoth_next_coupled_iff
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂) :
    let next :=
      profiledRawJointHybridShadowPhaseLiveTailSwitchBothNext A strategy hwin tag
        fallbackLeft fallbackRight one two input
    ProfiledRawJointHybridShadowPhaseLiveTailPhaseSwitchCoupled A strategy hwin
        tag fallbackLeft fallbackRight next.1 next.2 ↔
      ProfiledRawJointHybridShadowPhaseLiveTailBothConstructorCross A strategy
        hwin tag fallbackLeft fallbackRight one two input := by
  dsimp only
  constructor <;> intro h nextInput
  · simpa [ProfiledRawJointHybridShadowPhaseLiveTailPhaseSwitchCoupled,
      ProfiledRawJointHybridShadowPhaseLiveTailPhaseSwitchOutputCompatible,
      profiledRawJointHybridShadowPhaseLiveTailSwitchBothNext] using h nextInput
  · simpa [ProfiledRawJointHybridShadowPhaseLiveTailPhaseSwitchCoupled,
      ProfiledRawJointHybridShadowPhaseLiveTailPhaseSwitchOutputCompatible,
      profiledRawJointHybridShadowPhaseLiveTailSwitchBothNext] using h nextInput

end

end DetParityAutomaton

end DistributedSynthesis
