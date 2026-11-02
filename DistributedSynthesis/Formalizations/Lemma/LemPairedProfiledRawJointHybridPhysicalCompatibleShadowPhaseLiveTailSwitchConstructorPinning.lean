/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailSwitchOutputCouplingPreservationAudit

/-!
# Same-occurrence packets for the three tail switch constructors

The constructor audit isolates one cross-coordinate equation after each of
`strictRight`, `strictLeft`, and `both`.  This file gives the smallest useful
positive interface for discharging those equations.

A packet carries one finite represented guarded-common pair.  It does not ask
the two local processes to know a hierarchy side.  Its proof-only laws merely
say that the two physical coordinates selected at the following receive are
the corresponding root coordinates of that one pair.  The guarded root
anti-mosaic equations then close the constructor law immediately.

This distinction matters for the existing constructors.  Installing the
fresh receiver from a guarded occurrence pins only one side.  The continued
table is already one record below its root, so the old occurrence annotation
alone does not pin its next coordinate.  A simultaneous/dependent
preselection must make that continued coordinate the other projection of the
same packet.  The theorems below expose exactly that constructor contract; no
graph, orientation, leader bit, strict-leader bit, history, or semantic view
is supplied to an executable transition.
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

private abbrev CommonPair :=
  ProfiledRawJointGuardedCommonPair A strategy hwin

/-! ## Coordinate-minimal packets at an arbitrary successor -/

/-- A finite same-occurrence witness for the right-selected cross equation.
Only the right closing coordinate and the left informed coordinate are
pinned; neither whole record is required to agree. -/
def ProfiledRawJointHybridShadowPhaseLiveTailRightCrossPinned
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (next : OnePending A strategy hwin tag × TwoPending A strategy hwin tag) :
    Prop :=
  ∃ pair : CommonPair A strategy hwin,
    ∀ input : In₁ × In₂,
      let right :=
        profiledRawJointHybridShadowPhaseLiveTailSwitchRightRecord A strategy
          hwin tag fallbackRight next.1 next.2 input
      let left :=
        profiledRawJointHybridShadowPhaseLiveTailSwitchLeftRecord A strategy
          hwin tag fallbackLeft next.1 next.2 input
      right.physical.closingBoth =
          (pair.rightRootRecord A strategy hwin input).2.1.physical.closingBoth ∧
        pairedLeftInformedForRow .both left.physical =
          pairedLeftInformedForRow .both
            (pair.leftRootRecord A strategy hwin input).2.1.physical

/-- Mirror packet for the left-selected cross equation. -/
def ProfiledRawJointHybridShadowPhaseLiveTailLeftCrossPinned
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (next : OnePending A strategy hwin tag × TwoPending A strategy hwin tag) :
    Prop :=
  ∃ pair : CommonPair A strategy hwin,
    ∀ input : In₁ × In₂,
      let right :=
        profiledRawJointHybridShadowPhaseLiveTailSwitchRightRecord A strategy
          hwin tag fallbackRight next.1 next.2 input
      let left :=
        profiledRawJointHybridShadowPhaseLiveTailSwitchLeftRecord A strategy
          hwin tag fallbackLeft next.1 next.2 input
      left.physical.closingBoth =
          (pair.leftRootRecord A strategy hwin input).2.1.physical.closingBoth ∧
        pairedRightInformedForRow .both right.physical =
          pairedRightInformedForRow .both
            (pair.rightRootRecord A strategy hwin input).2.1.physical

/-- The right packet supplies the exact right/left anti-mosaic equation at
every following input. -/
theorem
    ProfiledRawJointHybridShadowPhaseLiveTailRightCrossPinned.cross
    {tag : Tag A strategy hwin} {fallbackLeft : LeftOutput A strategy hwin tag}
    {fallbackRight : RightOutput A strategy hwin tag}
    {next : OnePending A strategy hwin tag × TwoPending A strategy hwin tag}
    (hpinned :
      ProfiledRawJointHybridShadowPhaseLiveTailRightCrossPinned A strategy hwin
        tag fallbackLeft fallbackRight next)
    (input : In₁ × In₂) :
    let right :=
      profiledRawJointHybridShadowPhaseLiveTailSwitchRightRecord A strategy hwin
        tag fallbackRight next.1 next.2 input
    let left :=
      profiledRawJointHybridShadowPhaseLiveTailSwitchLeftRecord A strategy hwin
        tag fallbackLeft next.1 next.2 input
    right.physical.closingBoth =
      pairedLeftInformedForRow .both left.physical := by
  rcases hpinned with ⟨pair, hpinned⟩
  dsimp only
  calc
    _ = (pair.rightRootRecord A strategy hwin input).2.1.physical.closingBoth :=
      (hpinned input).1
    _ = pairedLeftInformedForRow .both
          (pair.leftRootRecord A strategy hwin input).2.1.physical :=
      pair.root_outputOne A strategy hwin input
    _ = _ := (hpinned input).2.symm

/-- Left mirror. -/
theorem
    ProfiledRawJointHybridShadowPhaseLiveTailLeftCrossPinned.cross
    {tag : Tag A strategy hwin} {fallbackLeft : LeftOutput A strategy hwin tag}
    {fallbackRight : RightOutput A strategy hwin tag}
    {next : OnePending A strategy hwin tag × TwoPending A strategy hwin tag}
    (hpinned :
      ProfiledRawJointHybridShadowPhaseLiveTailLeftCrossPinned A strategy hwin
        tag fallbackLeft fallbackRight next)
    (input : In₁ × In₂) :
    let right :=
      profiledRawJointHybridShadowPhaseLiveTailSwitchRightRecord A strategy hwin
        tag fallbackRight next.1 next.2 input
    let left :=
      profiledRawJointHybridShadowPhaseLiveTailSwitchLeftRecord A strategy hwin
        tag fallbackLeft next.1 next.2 input
    left.physical.closingBoth =
      pairedRightInformedForRow .both right.physical := by
  rcases hpinned with ⟨pair, hpinned⟩
  dsimp only
  calc
    _ = (pair.leftRootRecord A strategy hwin input).2.1.physical.closingBoth :=
      (hpinned input).1
    _ = pairedRightInformedForRow .both
          (pair.rightRootRecord A strategy hwin input).2.1.physical :=
      pair.root_outputTwo A strategy hwin input
    _ = _ := (hpinned input).2.symm

/-! ## Exact residual after one fresh side is installed -/

/-- If the fresh left receiver is already pinned to a represented pair, the
right-selected anti-mosaic law is equivalent to one equation for the
continued right coordinate.  This is the strict-right constructor's exact
required equation. -/
theorem
    profiledRawJointHybridShadowPhaseLiveTail_rightCross_iff_continued_of_freshLeft
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (next : OnePending A strategy hwin tag × TwoPending A strategy hwin tag)
    (pair : CommonPair A strategy hwin)
    (hfresh : ∀ input : In₁ × In₂,
      let left :=
        profiledRawJointHybridShadowPhaseLiveTailSwitchLeftRecord A strategy
          hwin tag fallbackLeft next.1 next.2 input
      pairedLeftInformedForRow .both left.physical =
        pairedLeftInformedForRow .both
          (pair.leftRootRecord A strategy hwin input).2.1.physical) :
    (∀ input : In₁ × In₂,
        let right :=
          profiledRawJointHybridShadowPhaseLiveTailSwitchRightRecord A strategy
            hwin tag fallbackRight next.1 next.2 input
        let left :=
          profiledRawJointHybridShadowPhaseLiveTailSwitchLeftRecord A strategy
            hwin tag fallbackLeft next.1 next.2 input
        right.physical.closingBoth =
          pairedLeftInformedForRow .both left.physical) ↔
      (∀ input : In₁ × In₂,
        let right :=
          profiledRawJointHybridShadowPhaseLiveTailSwitchRightRecord A strategy
            hwin tag fallbackRight next.1 next.2 input
        right.physical.closingBoth =
          (pair.rightRootRecord A strategy hwin input).2.1.physical.closingBoth) := by
  constructor
  · intro h input
    calc
      _ = pairedLeftInformedForRow .both
            (profiledRawJointHybridShadowPhaseLiveTailSwitchLeftRecord A
              strategy hwin tag fallbackLeft next.1 next.2 input).physical :=
        h input
      _ = pairedLeftInformedForRow .both
            (pair.leftRootRecord A strategy hwin input).2.1.physical :=
        hfresh input
      _ = _ := (pair.root_outputOne A strategy hwin input).symm
  · intro h input
    calc
      _ = (pair.rightRootRecord A strategy hwin input).2.1.physical.closingBoth :=
        h input
      _ = pairedLeftInformedForRow .both
            (pair.leftRootRecord A strategy hwin input).2.1.physical :=
        pair.root_outputOne A strategy hwin input
      _ = pairedLeftInformedForRow .both
            (profiledRawJointHybridShadowPhaseLiveTailSwitchLeftRecord A
              strategy hwin tag fallbackLeft next.1 next.2 input).physical :=
        (hfresh input).symm

/-- Strict-left mirror: after the fresh right receiver is root-pinned, only
the continued left closing coordinate remains. -/
theorem
    profiledRawJointHybridShadowPhaseLiveTail_leftCross_iff_continued_of_freshRight
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (next : OnePending A strategy hwin tag × TwoPending A strategy hwin tag)
    (pair : CommonPair A strategy hwin)
    (hfresh : ∀ input : In₁ × In₂,
      let right :=
        profiledRawJointHybridShadowPhaseLiveTailSwitchRightRecord A strategy
          hwin tag fallbackRight next.1 next.2 input
      pairedRightInformedForRow .both right.physical =
        pairedRightInformedForRow .both
          (pair.rightRootRecord A strategy hwin input).2.1.physical) :
    (∀ input : In₁ × In₂,
        let right :=
          profiledRawJointHybridShadowPhaseLiveTailSwitchRightRecord A strategy
            hwin tag fallbackRight next.1 next.2 input
        let left :=
          profiledRawJointHybridShadowPhaseLiveTailSwitchLeftRecord A strategy
            hwin tag fallbackLeft next.1 next.2 input
        left.physical.closingBoth =
          pairedRightInformedForRow .both right.physical) ↔
      (∀ input : In₁ × In₂,
        let left :=
          profiledRawJointHybridShadowPhaseLiveTailSwitchLeftRecord A strategy
            hwin tag fallbackLeft next.1 next.2 input
        left.physical.closingBoth =
          (pair.leftRootRecord A strategy hwin input).2.1.physical.closingBoth) := by
  constructor
  · intro h input
    calc
      _ = pairedRightInformedForRow .both
            (profiledRawJointHybridShadowPhaseLiveTailSwitchRightRecord A
              strategy hwin tag fallbackRight next.1 next.2 input).physical :=
        h input
      _ = pairedRightInformedForRow .both
            (pair.rightRootRecord A strategy hwin input).2.1.physical :=
        hfresh input
      _ = _ := (pair.root_outputTwo A strategy hwin input).symm
  · intro h input
    calc
      _ = (pair.leftRootRecord A strategy hwin input).2.1.physical.closingBoth :=
        h input
      _ = pairedRightInformedForRow .both
            (pair.rightRootRecord A strategy hwin input).2.1.physical :=
        pair.root_outputTwo A strategy hwin input
      _ = pairedRightInformedForRow .both
            (profiledRawJointHybridShadowPhaseLiveTailSwitchRightRecord A
              strategy hwin tag fallbackRight next.1 next.2 input).physical :=
        (hfresh input).symm

/-- Carrying both coordinate packets at one successor gives the full
phase-indexed coupling, regardless of the phase stored there. -/
structure ProfiledRawJointHybridShadowPhaseLiveTailSuccessorCrossPinning
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (next : OnePending A strategy hwin tag × TwoPending A strategy hwin tag) :
    Prop where
  right :
    ProfiledRawJointHybridShadowPhaseLiveTailRightCrossPinned A strategy hwin
      tag fallbackLeft fallbackRight next
  left :
    ProfiledRawJointHybridShadowPhaseLiveTailLeftCrossPinned A strategy hwin
      tag fallbackLeft fallbackRight next

theorem
    ProfiledRawJointHybridShadowPhaseLiveTailSuccessorCrossPinning.coupled
    {tag : Tag A strategy hwin} {fallbackLeft : LeftOutput A strategy hwin tag}
    {fallbackRight : RightOutput A strategy hwin tag}
    {next : OnePending A strategy hwin tag × TwoPending A strategy hwin tag}
    (hpinned :
      ProfiledRawJointHybridShadowPhaseLiveTailSuccessorCrossPinning A strategy
        hwin tag fallbackLeft fallbackRight next) :
    ProfiledRawJointHybridShadowPhaseLiveTailPhaseSwitchCoupled A strategy hwin
      tag fallbackLeft fallbackRight next.1 next.2 := by
  intro input
  unfold
    ProfiledRawJointHybridShadowPhaseLiveTailPhaseSwitchOutputCompatible
  split
  · exact hpinned.left.cross A strategy hwin input
  · exact hpinned.right.cross A strategy hwin input

/-! ## Full record pinning is a sufficient producer -/

/-- Stronger but often convenient constructor contract: both selected
physical records are roots of one finite represented pair. -/
def ProfiledRawJointHybridShadowPhaseLiveTailSuccessorPinnedToPair
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (next : OnePending A strategy hwin tag × TwoPending A strategy hwin tag)
    (pair : CommonPair A strategy hwin) : Prop :=
  ∀ input : In₁ × In₂,
    let right :=
      profiledRawJointHybridShadowPhaseLiveTailSwitchRightRecord A strategy hwin
        tag fallbackRight next.1 next.2 input
    let left :=
      profiledRawJointHybridShadowPhaseLiveTailSwitchLeftRecord A strategy hwin
        tag fallbackLeft next.1 next.2 input
    right.physical =
        (pair.rightRootRecord A strategy hwin input).2.1.physical ∧
      left.physical =
        (pair.leftRootRecord A strategy hwin input).2.1.physical

theorem
    ProfiledRawJointHybridShadowPhaseLiveTailSuccessorPinnedToPair.rightCrossPinned
    {tag : Tag A strategy hwin} {fallbackLeft : LeftOutput A strategy hwin tag}
    {fallbackRight : RightOutput A strategy hwin tag}
    {next : OnePending A strategy hwin tag × TwoPending A strategy hwin tag}
    {pair : CommonPair A strategy hwin}
    (hpinned :
      ProfiledRawJointHybridShadowPhaseLiveTailSuccessorPinnedToPair A strategy
        hwin tag fallbackLeft fallbackRight next pair) :
    ProfiledRawJointHybridShadowPhaseLiveTailRightCrossPinned A strategy hwin
      tag fallbackLeft fallbackRight next := by
  refine ⟨pair, ?_⟩
  intro input
  have h := hpinned input
  exact ⟨congrArg (fun physical ↦ physical.closingBoth) h.1,
    congrArg (pairedLeftInformedForRow .both) h.2⟩

theorem
    ProfiledRawJointHybridShadowPhaseLiveTailSuccessorPinnedToPair.leftCrossPinned
    {tag : Tag A strategy hwin} {fallbackLeft : LeftOutput A strategy hwin tag}
    {fallbackRight : RightOutput A strategy hwin tag}
    {next : OnePending A strategy hwin tag × TwoPending A strategy hwin tag}
    {pair : CommonPair A strategy hwin}
    (hpinned :
      ProfiledRawJointHybridShadowPhaseLiveTailSuccessorPinnedToPair A strategy
        hwin tag fallbackLeft fallbackRight next pair) :
    ProfiledRawJointHybridShadowPhaseLiveTailLeftCrossPinned A strategy hwin
      tag fallbackLeft fallbackRight next := by
  refine ⟨pair, ?_⟩
  intro input
  have h := hpinned input
  exact ⟨congrArg (fun physical ↦ physical.closingBoth) h.2,
    congrArg (pairedRightInformedForRow .both) h.1⟩

theorem
    ProfiledRawJointHybridShadowPhaseLiveTailSuccessorPinnedToPair.crossPinning
    {tag : Tag A strategy hwin} {fallbackLeft : LeftOutput A strategy hwin tag}
    {fallbackRight : RightOutput A strategy hwin tag}
    {next : OnePending A strategy hwin tag × TwoPending A strategy hwin tag}
    {pair : CommonPair A strategy hwin}
    (hpinned :
      ProfiledRawJointHybridShadowPhaseLiveTailSuccessorPinnedToPair A strategy
        hwin tag fallbackLeft fallbackRight next pair) :
    ProfiledRawJointHybridShadowPhaseLiveTailSuccessorCrossPinning A strategy
      hwin tag fallbackLeft fallbackRight next :=
  ⟨hpinned.rightCrossPinned A strategy hwin,
    hpinned.leftCrossPinned A strategy hwin⟩

/-! ## The three audited constructors -/

/-- A strict-right successor packet closes the exact constructor field. -/
theorem
    profiledRawJointHybridShadowPhaseLiveTailStrictRightConstructorCross_of_pinned
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂)
    (hpinned :
      ProfiledRawJointHybridShadowPhaseLiveTailRightCrossPinned A strategy hwin
        tag fallbackLeft fallbackRight
        (profiledRawJointHybridShadowPhaseLiveTailSwitchStrictRightNext A
          strategy hwin tag fallbackLeft fallbackRight one two input)) :
    ProfiledRawJointHybridShadowPhaseLiveTailStrictRightConstructorCross A
      strategy hwin tag fallbackLeft fallbackRight one two input := by
  intro nextInput
  exact hpinned.cross A strategy hwin nextInput

/-- Strict-left mirror. -/
theorem
    profiledRawJointHybridShadowPhaseLiveTailStrictLeftConstructorCross_of_pinned
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂)
    (hpinned :
      ProfiledRawJointHybridShadowPhaseLiveTailLeftCrossPinned A strategy hwin
        tag fallbackLeft fallbackRight
        (profiledRawJointHybridShadowPhaseLiveTailSwitchStrictLeftNext A
          strategy hwin tag fallbackLeft fallbackRight one two input)) :
    ProfiledRawJointHybridShadowPhaseLiveTailStrictLeftConstructorCross A
      strategy hwin tag fallbackLeft fallbackRight one two input := by
  intro nextInput
  exact hpinned.cross A strategy hwin nextInput

/-- A simultaneous successor uses the same left-selected packet. -/
theorem
    profiledRawJointHybridShadowPhaseLiveTailBothConstructorCross_of_pinned
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂)
    (hpinned :
      ProfiledRawJointHybridShadowPhaseLiveTailLeftCrossPinned A strategy hwin
        tag fallbackLeft fallbackRight
        (profiledRawJointHybridShadowPhaseLiveTailSwitchBothNext A strategy hwin
          tag fallbackLeft fallbackRight one two input)) :
    ProfiledRawJointHybridShadowPhaseLiveTailBothConstructorCross A strategy
      hwin tag fallbackLeft fallbackRight one two input := by
  intro nextInput
  exact hpinned.cross A strategy hwin nextInput

/-! ## One package closes preservation for all three constructors -/

/-- Proof-only constructor contract for an operational tail step.  Each
field is one finite same-occurrence packet; no field is an executable side
test. -/
structure ProfiledRawJointHybridShadowPhaseLiveTailConstructorPinning
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂) : Prop where
  strictRight :
    ProfiledRawJointHybridShadowPhaseLiveTailRightCrossPinned A strategy hwin
      tag fallbackLeft fallbackRight
      (profiledRawJointHybridShadowPhaseLiveTailSwitchStrictRightNext A
        strategy hwin tag fallbackLeft fallbackRight one two input)
  strictLeft :
    ProfiledRawJointHybridShadowPhaseLiveTailLeftCrossPinned A strategy hwin
      tag fallbackLeft fallbackRight
      (profiledRawJointHybridShadowPhaseLiveTailSwitchStrictLeftNext A strategy
        hwin tag fallbackLeft fallbackRight one two input)
  both :
    ProfiledRawJointHybridShadowPhaseLiveTailLeftCrossPinned A strategy hwin
      tag fallbackLeft fallbackRight
      (profiledRawJointHybridShadowPhaseLiveTailSwitchBothNext A strategy hwin
        tag fallbackLeft fallbackRight one two input)

theorem
    ProfiledRawJointHybridShadowPhaseLiveTailConstructorPinning.constructorCrosses
    {tag : Tag A strategy hwin} {fallbackLeft : LeftOutput A strategy hwin tag}
    {fallbackRight : RightOutput A strategy hwin tag}
    {one : OnePending A strategy hwin tag}
    {two : TwoPending A strategy hwin tag} {input : In₁ × In₂}
    (hpinned :
      ProfiledRawJointHybridShadowPhaseLiveTailConstructorPinning A strategy
        hwin tag fallbackLeft fallbackRight one two input) :
    ProfiledRawJointHybridShadowPhaseLiveTailStrictRightConstructorCross A
          strategy hwin tag fallbackLeft fallbackRight one two input ∧
      ProfiledRawJointHybridShadowPhaseLiveTailStrictLeftConstructorCross A
          strategy hwin tag fallbackLeft fallbackRight one two input ∧
      ProfiledRawJointHybridShadowPhaseLiveTailBothConstructorCross A strategy
          hwin tag fallbackLeft fallbackRight one two input := by
  exact ⟨
    profiledRawJointHybridShadowPhaseLiveTailStrictRightConstructorCross_of_pinned
      A strategy hwin tag fallbackLeft fallbackRight one two input
        hpinned.strictRight,
    profiledRawJointHybridShadowPhaseLiveTailStrictLeftConstructorCross_of_pinned
      A strategy hwin tag fallbackLeft fallbackRight one two input
        hpinned.strictLeft,
    profiledRawJointHybridShadowPhaseLiveTailBothConstructorCross_of_pinned A
      strategy hwin tag fallbackLeft fallbackRight one two input hpinned.both⟩

end

end DetParityAutomaton

end DistributedSynthesis
