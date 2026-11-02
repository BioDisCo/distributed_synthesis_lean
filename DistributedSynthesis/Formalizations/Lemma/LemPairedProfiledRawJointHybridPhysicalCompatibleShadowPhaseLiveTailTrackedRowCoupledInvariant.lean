/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailRowAwareSwitch
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailRowTimingAudit

/-!
# Tracked and row-coupled recurrent Tail states

This is the induction shell for the repaired Tail argument.  It combines the
already-proved literal/tracked invariant with the row-aware cross law.  Each
of the three concrete constructors preserves the conjunction from exactly
one constructor-cross premise.

The premises are proof-side semantic facts.  No constructor below receives a
graph, hierarchy side, leader bit, strict-leader bit, history, or semantic
view.  In particular, this file does not attempt to infer the strict side in
either endpoint controller.

Downstream audit: `TailTrackedTrace` uses only the first conjunct and remains
valid as a literal-prefix trace.  Its old physical output seam does *not*
consume this conjunction: `TailSwitchOutputOne/Two` and
`TailPendingBothOutputOne/Two` hard-code `.both`.  Therefore physical
readback must use a row-aware controller (the retained-carrier trace), rather
than recovering correctness by changing only a proof predicate.  The
resolved-cut schedule and row-parametric packet bridges remain reusable once
fed the repaired physical trace.
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

/-- The exact proof invariant needed by the repaired recurrent Tail trace. -/
def ProfiledRawJointHybridShadowPhaseLiveTailTrackedRowCoupled
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) : Prop :=
  ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant A strategy hwin tag
      one two ∧
    ProfiledRawJointHybridShadowPhaseLiveTailRowSwitchCoupled A strategy hwin
      tag fallbackLeft fallbackRight one two

theorem ProfiledRawJointHybridShadowPhaseLiveTailTrackedRowCoupled.tracked
    {tag : Tag A strategy hwin} {fallbackLeft : LeftOutput A strategy hwin tag}
    {fallbackRight : RightOutput A strategy hwin tag}
    {one : OnePending A strategy hwin tag}
    {two : TwoPending A strategy hwin tag}
    (h :
      ProfiledRawJointHybridShadowPhaseLiveTailTrackedRowCoupled A strategy hwin
        tag fallbackLeft fallbackRight one two) :
    ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant A strategy hwin
      tag one two :=
  h.1

theorem ProfiledRawJointHybridShadowPhaseLiveTailTrackedRowCoupled.rowCoupled
    {tag : Tag A strategy hwin} {fallbackLeft : LeftOutput A strategy hwin tag}
    {fallbackRight : RightOutput A strategy hwin tag}
    {one : OnePending A strategy hwin tag}
    {two : TwoPending A strategy hwin tag}
    (h :
      ProfiledRawJointHybridShadowPhaseLiveTailTrackedRowCoupled A strategy hwin
        tag fallbackLeft fallbackRight one two) :
    ProfiledRawJointHybridShadowPhaseLiveTailRowSwitchCoupled A strategy hwin
      tag fallbackLeft fallbackRight one two :=
  h.2

/-! ## Exact one-step induction shell -/

theorem
    ProfiledRawJointHybridShadowPhaseLiveTailTrackedRowCoupled.strictRight
    {tag : Tag A strategy hwin} {fallbackLeft : LeftOutput A strategy hwin tag}
    {fallbackRight : RightOutput A strategy hwin tag}
    {one : OnePending A strategy hwin tag}
    {two : TwoPending A strategy hwin tag}
    (hcurrent :
      ProfiledRawJointHybridShadowPhaseLiveTailTrackedRowCoupled A strategy hwin
        tag fallbackLeft fallbackRight one two)
    (input : In₁ × In₂)
    (hcross :
      ProfiledRawJointHybridShadowPhaseLiveTailRowStrictRightConstructorCross A
        strategy hwin tag fallbackLeft fallbackRight one two input) :
    let next :=
      profiledRawJointHybridShadowPhaseLiveTailSwitchStrictRightNext A strategy
        hwin tag fallbackLeft fallbackRight one two input
    ProfiledRawJointHybridShadowPhaseLiveTailTrackedRowCoupled A strategy hwin
      tag fallbackLeft fallbackRight next.1 next.2 := by
  dsimp only
  constructor
  · exact
      ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant.strictRight.{u,
        v, x, y, s, max u v x y s, max u v x y s, max u v x y s,
        max u v x y s, max u v x y s, max u v x y s,
        max u v x y s, max u v x y s} A strategy hwin hcurrent.1
          fallbackLeft fallbackRight input
  · exact
      (profiledRawJointHybridShadowPhaseLiveTailStrictRight_next_rowCoupled_iff
        A strategy hwin tag fallbackLeft fallbackRight one two input).2 hcross

theorem
    ProfiledRawJointHybridShadowPhaseLiveTailTrackedRowCoupled.strictLeft
    {tag : Tag A strategy hwin} {fallbackLeft : LeftOutput A strategy hwin tag}
    {fallbackRight : RightOutput A strategy hwin tag}
    {one : OnePending A strategy hwin tag}
    {two : TwoPending A strategy hwin tag}
    (hcurrent :
      ProfiledRawJointHybridShadowPhaseLiveTailTrackedRowCoupled A strategy hwin
        tag fallbackLeft fallbackRight one two)
    (input : In₁ × In₂)
    (hcross :
      ProfiledRawJointHybridShadowPhaseLiveTailRowStrictLeftConstructorCross A
        strategy hwin tag fallbackLeft fallbackRight one two input) :
    let next :=
      profiledRawJointHybridShadowPhaseLiveTailSwitchStrictLeftNext A strategy
        hwin tag fallbackLeft fallbackRight one two input
    ProfiledRawJointHybridShadowPhaseLiveTailTrackedRowCoupled A strategy hwin
      tag fallbackLeft fallbackRight next.1 next.2 := by
  dsimp only
  constructor
  · exact
      ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant.strictLeft.{u,
        v, x, y, s, max u v x y s, max u v x y s, max u v x y s,
        max u v x y s, max u v x y s, max u v x y s,
        max u v x y s, max u v x y s} A strategy hwin hcurrent.1
          fallbackLeft fallbackRight input
  · exact
      (profiledRawJointHybridShadowPhaseLiveTailStrictLeft_next_rowCoupled_iff
        A strategy hwin tag fallbackLeft fallbackRight one two input).2 hcross

theorem ProfiledRawJointHybridShadowPhaseLiveTailTrackedRowCoupled.both
    {tag : Tag A strategy hwin} {fallbackLeft : LeftOutput A strategy hwin tag}
    {fallbackRight : RightOutput A strategy hwin tag}
    {one : OnePending A strategy hwin tag}
    {two : TwoPending A strategy hwin tag}
    (hcurrent :
      ProfiledRawJointHybridShadowPhaseLiveTailTrackedRowCoupled A strategy hwin
        tag fallbackLeft fallbackRight one two)
    (input : In₁ × In₂)
    (hcross :
      ProfiledRawJointHybridShadowPhaseLiveTailRowBothConstructorCross A
        strategy hwin tag fallbackLeft fallbackRight one two input) :
    let next :=
      profiledRawJointHybridShadowPhaseLiveTailSwitchBothNext A strategy hwin
        tag fallbackLeft fallbackRight one two input
    ProfiledRawJointHybridShadowPhaseLiveTailTrackedRowCoupled A strategy hwin
      tag fallbackLeft fallbackRight next.1 next.2 := by
  dsimp only
  constructor
  · exact
      profiledRawJointHybridShadowPhaseLiveTailFreshPair_closed_trackedInvariant.{u,
        v, x, y, s, max u v x y s, max u v x y s, max u v x y s,
        max u v x y s, max u v x y s, max u v x y s,
        max u v x y s, max u v x y s} A strategy hwin tag fallbackLeft
          fallbackRight one two input hcurrent.1
  · exact
      (profiledRawJointHybridShadowPhaseLiveTailBoth_next_rowCoupled_iff A
        strategy hwin tag fallbackLeft fallbackRight one two input).2 hcross

/-! ## One named socket for the remaining semantic constructor proof -/

/-- A proof-side family of constructor-cross facts.  Once the literal
current-table adapter supplies this structure, the combined invariant closes
under every graph letter without any further controller mathematics. -/
structure ProfiledRawJointHybridShadowPhaseLiveTailRowConstructorClosure
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag) : Prop where
  strictRight : ∀ (one : OnePending A strategy hwin tag)
      (two : TwoPending A strategy hwin tag) (input : In₁ × In₂),
    ProfiledRawJointHybridShadowPhaseLiveTailTrackedRowCoupled A strategy hwin
        tag fallbackLeft fallbackRight one two →
      ProfiledRawJointHybridShadowPhaseLiveTailRowStrictRightConstructorCross A
        strategy hwin tag fallbackLeft fallbackRight one two input
  strictLeft : ∀ (one : OnePending A strategy hwin tag)
      (two : TwoPending A strategy hwin tag) (input : In₁ × In₂),
    ProfiledRawJointHybridShadowPhaseLiveTailTrackedRowCoupled A strategy hwin
        tag fallbackLeft fallbackRight one two →
      ProfiledRawJointHybridShadowPhaseLiveTailRowStrictLeftConstructorCross A
        strategy hwin tag fallbackLeft fallbackRight one two input
  both : ∀ (one : OnePending A strategy hwin tag)
      (two : TwoPending A strategy hwin tag) (input : In₁ × In₂),
    ProfiledRawJointHybridShadowPhaseLiveTailTrackedRowCoupled A strategy hwin
        tag fallbackLeft fallbackRight one two →
      ProfiledRawJointHybridShadowPhaseLiveTailRowBothConstructorCross A
        strategy hwin tag fallbackLeft fallbackRight one two input

theorem
    ProfiledRawJointHybridShadowPhaseLiveTailTrackedRowCoupled.strictRight_of_closure
    {tag : Tag A strategy hwin} {fallbackLeft : LeftOutput A strategy hwin tag}
    {fallbackRight : RightOutput A strategy hwin tag}
    {one : OnePending A strategy hwin tag}
    {two : TwoPending A strategy hwin tag}
    (closure :
      ProfiledRawJointHybridShadowPhaseLiveTailRowConstructorClosure A strategy
        hwin tag fallbackLeft fallbackRight)
    (hcurrent :
      ProfiledRawJointHybridShadowPhaseLiveTailTrackedRowCoupled A strategy hwin
        tag fallbackLeft fallbackRight one two)
    (input : In₁ × In₂) :
    let next :=
      profiledRawJointHybridShadowPhaseLiveTailSwitchStrictRightNext A strategy
        hwin tag fallbackLeft fallbackRight one two input
    ProfiledRawJointHybridShadowPhaseLiveTailTrackedRowCoupled A strategy hwin
      tag fallbackLeft fallbackRight next.1 next.2 :=
  hcurrent.strictRight A strategy hwin input
    (closure.strictRight one two input hcurrent)

theorem
    ProfiledRawJointHybridShadowPhaseLiveTailTrackedRowCoupled.strictLeft_of_closure
    {tag : Tag A strategy hwin} {fallbackLeft : LeftOutput A strategy hwin tag}
    {fallbackRight : RightOutput A strategy hwin tag}
    {one : OnePending A strategy hwin tag}
    {two : TwoPending A strategy hwin tag}
    (closure :
      ProfiledRawJointHybridShadowPhaseLiveTailRowConstructorClosure A strategy
        hwin tag fallbackLeft fallbackRight)
    (hcurrent :
      ProfiledRawJointHybridShadowPhaseLiveTailTrackedRowCoupled A strategy hwin
        tag fallbackLeft fallbackRight one two)
    (input : In₁ × In₂) :
    let next :=
      profiledRawJointHybridShadowPhaseLiveTailSwitchStrictLeftNext A strategy
        hwin tag fallbackLeft fallbackRight one two input
    ProfiledRawJointHybridShadowPhaseLiveTailTrackedRowCoupled A strategy hwin
      tag fallbackLeft fallbackRight next.1 next.2 :=
  hcurrent.strictLeft A strategy hwin input
    (closure.strictLeft one two input hcurrent)

theorem
    ProfiledRawJointHybridShadowPhaseLiveTailTrackedRowCoupled.both_of_closure
    {tag : Tag A strategy hwin} {fallbackLeft : LeftOutput A strategy hwin tag}
    {fallbackRight : RightOutput A strategy hwin tag}
    {one : OnePending A strategy hwin tag}
    {two : TwoPending A strategy hwin tag}
    (closure :
      ProfiledRawJointHybridShadowPhaseLiveTailRowConstructorClosure A strategy
        hwin tag fallbackLeft fallbackRight)
    (hcurrent :
      ProfiledRawJointHybridShadowPhaseLiveTailTrackedRowCoupled A strategy hwin
        tag fallbackLeft fallbackRight one two)
    (input : In₁ × In₂) :
    let next :=
      profiledRawJointHybridShadowPhaseLiveTailSwitchBothNext A strategy hwin
        tag fallbackLeft fallbackRight one two input
    ProfiledRawJointHybridShadowPhaseLiveTailTrackedRowCoupled A strategy hwin
      tag fallbackLeft fallbackRight next.1 next.2 :=
  hcurrent.both A strategy hwin input (closure.both one two input hcurrent)

end

end DetParityAutomaton

end DistributedSynthesis
