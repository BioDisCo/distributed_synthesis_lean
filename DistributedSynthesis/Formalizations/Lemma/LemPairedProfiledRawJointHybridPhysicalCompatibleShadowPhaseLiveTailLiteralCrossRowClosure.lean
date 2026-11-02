/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailRowConstructorClosure
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailLiteralCrossConstructorBridge

/-!
# One literal-cross socket closes the row-aware Tail constructors

The tracked Tail invariant already proves both strict constructor equations.
For a simultaneous close, row timing proves that the two freshly selected
receiver rows are `.both`.  Consequently the old literal-cross constructor
equation is exactly the remaining row-aware equation.

This file packages that reduction.  A `TailBothLiteralCrossInstallation`
selects one reachable decorated-policy successor and asserts that the
simultaneous Tail constructor installs its two retained literal roots.  The
existing same-occurrence anti-mosaic theorem then supplies the complete
`RowConstructorClosure`.

No executable transition receives the selected policy state, incoming
letter, anchors, graph, orientation, hierarchy side, or semantic view.
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

/-! ## The old simultaneous equation is already row-aware -/

/-- On a tracked simultaneous successor, the two effective rows are `.both`.
Thus the literal-cross simultaneous constructor equation is precisely its
row-aware form. -/
theorem
    profiledRawJointHybridShadowPhaseLiveTailRowBothConstructorCross_of_tracked_of_bothConstructorCross
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂)
    (hinvariant :
      ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant A strategy hwin
        tag one two)
    (hcross :
      ProfiledRawJointHybridShadowPhaseLiveTailBothConstructorCross A strategy
        hwin tag fallbackLeft fallbackRight one two input) :
    ProfiledRawJointHybridShadowPhaseLiveTailRowBothConstructorCross A strategy
      hwin tag fallbackLeft fallbackRight one two input := by
  intro nextInput
  have hrows :=
    profiledRawJointHybridShadowPhaseLiveTailSwitchBothNext_closedRows A
      strategy hwin tag fallbackLeft fallbackRight one two input hinvariant
  dsimp only at hrows
  simp only [profiledRawJointHybridShadowPhaseLiveTailSwitchLeftRow,
    profiledRawJointHybridShadowPhaseLiveTailSwitchRightRow]
  rw [hrows.1, hrows.2]
  simpa [pairedLeftClosingForRow] using hcross nextInput

/-- The two strict fields are automatic from tracking.  Therefore a family
of old simultaneous constructor crosses is the only semantic input needed
for the complete row-aware closure. -/
theorem
    profiledRawJointHybridShadowPhaseLiveTailRowConstructorClosure_of_bothConstructorCross
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (hboth : ∀ (one : OnePending A strategy hwin tag)
        (two : TwoPending A strategy hwin tag) (input : In₁ × In₂),
      ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant A strategy hwin
          tag one two →
        ProfiledRawJointHybridShadowPhaseLiveTailBothConstructorCross A
          strategy hwin tag fallbackLeft fallbackRight one two input) :
    ProfiledRawJointHybridShadowPhaseLiveTailRowConstructorClosure A strategy
      hwin tag fallbackLeft fallbackRight where
  strictRight one two input hcurrent :=
    ProfiledRawJointHybridShadowPhaseLiveTailRowStrictRightConstructorCross_of_tracked
      A strategy hwin tag fallbackLeft fallbackRight one two input hcurrent.1
  strictLeft one two input hcurrent :=
    ProfiledRawJointHybridShadowPhaseLiveTailRowStrictLeftConstructorCross_of_tracked
      A strategy hwin tag fallbackLeft fallbackRight one two input hcurrent.1
  both one two input hcurrent :=
    profiledRawJointHybridShadowPhaseLiveTailRowBothConstructorCross_of_tracked_of_bothConstructorCross
      A strategy hwin tag fallbackLeft fallbackRight one two input hcurrent.1
        (hboth one two input hcurrent.1)

/-! ## Exact one-field literal installation interface -/

namespace ProfiledRawJointGuardedCommonDecoratedPolicyPackage

variable {initial : CommonPoint A strategy}

/-- Proof-side finite data saying that every tracked simultaneous successor
installs the two literal-cross roots retained at one reachable successor of
the same decorated policy.  This is the exact anti-mosaic construction still
owed by an executable Tail implementation. -/
structure ProfiledRawJointHybridShadowPhaseLiveTailBothLiteralCrossInstallation
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag) where
  stateAt : OnePending A strategy hwin tag →
    TwoPending A strategy hwin tag → In₁ × In₂ →
      ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin initial
        (CrossValid A strategy hwin)
  reachableAt : ∀ one two input,
    ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
      initial (CrossValid A strategy hwin) package.policy
        (stateAt one two input)
  incomingAt : OnePending A strategy hwin tag →
    TwoPending A strategy hwin tag → In₁ × In₂ → In₁ × In₂
  rightAnchorAt : OnePending A strategy hwin tag →
    TwoPending A strategy hwin tag → In₁ × In₂ → Bool
  leftAnchorAt : OnePending A strategy hwin tag →
    TwoPending A strategy hwin tag → In₁ × In₂ → Bool
  matchAt : ∀ one two input,
    ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant A strategy hwin
        tag one two →
      package.TailNextMatchesLiteralCrossRoots A strategy hwin
        (stateAt one two input) (incomingAt one two input) tag fallbackLeft
          fallbackRight
          (profiledRawJointHybridShadowPhaseLiveTailSwitchBothNext A strategy
            hwin tag fallbackLeft fallbackRight one two input)
          (rightAnchorAt one two input) (leftAnchorAt one two input)

/-- A literal-cross simultaneous installer closes all three row-aware Tail
constructor fields. -/
theorem
    ProfiledRawJointHybridShadowPhaseLiveTailBothLiteralCrossInstallation.rowConstructorClosure
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (install :
      ProfiledRawJointHybridShadowPhaseLiveTailBothLiteralCrossInstallation A
        strategy hwin package tag fallbackLeft fallbackRight) :
    ProfiledRawJointHybridShadowPhaseLiveTailRowConstructorClosure A strategy
      hwin tag fallbackLeft fallbackRight := by
  apply
    profiledRawJointHybridShadowPhaseLiveTailRowConstructorClosure_of_bothConstructorCross
      A strategy hwin tag fallbackLeft fallbackRight
  intro one two input hinvariant
  exact package.tailBothConstructorCross_of_matchesLiteralCrossRoots A strategy
    hwin (install.reachableAt one two input) (install.incomingAt one two input)
      tag fallbackLeft fallbackRight one two input
      (install.rightAnchorAt one two input) (install.leftAnchorAt one two input)
      (install.matchAt one two input hinvariant)

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
