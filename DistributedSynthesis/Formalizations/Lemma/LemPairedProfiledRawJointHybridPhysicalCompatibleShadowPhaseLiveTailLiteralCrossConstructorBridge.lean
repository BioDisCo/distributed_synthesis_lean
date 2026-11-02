/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossRootPhysical

/-!
# Literal-root adapters for the three live-tail constructors

The retained literal-cross tables already pin both complete receiver roots to
one represented guarded-common pair.  This file connects that operational
root theorem to each of the three constructor laws used by the phase-live
tail.

The only remaining premise in each theorem is the literal finite-state
installation equation `TailNextMatchesLiteralCrossRoots`.  No semantic output
equality remains: once the two next Tail records are those two installed
literal roots, the guarded-pair anti-mosaic law proves the constructor cross.
No executable transition is given a graph, hierarchy side, leader bit,
strict-leader bit, history, or semantic view.
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

namespace ProfiledRawJointGuardedCommonDecoratedPolicyPackage

variable {initial : CommonPoint A strategy}

/-! ## Constructor-by-constructor consumption -/

/-- A strict-right successor satisfying the finite literal-root installation
equation satisfies the exact strict-right constructor cross. -/
theorem tailStrictRightConstructorCross_of_matchesLiteralCrossRoots
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    {state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial (CrossValid A strategy hwin)}
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial (CrossValid A strategy hwin) package.policy state)
    (incoming : In₁ × In₂)
    (tag : Tag A strategy hwin)
    (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂)
    (rightAnchor leftAnchor : Bool)
    (hmatch : package.TailNextMatchesLiteralCrossRoots A strategy hwin state
      incoming tag fallbackLeft fallbackRight
        (profiledRawJointHybridShadowPhaseLiveTailSwitchStrictRightNext A
          strategy hwin tag fallbackLeft fallbackRight one two input)
        rightAnchor leftAnchor) :
    ProfiledRawJointHybridShadowPhaseLiveTailStrictRightConstructorCross A
      strategy hwin tag fallbackLeft fallbackRight one two input := by
  apply
    profiledRawJointHybridShadowPhaseLiveTailStrictRightConstructorCross_of_pinned
  exact
    (package.tailSuccessorPinnedToPair_of_matchesLiteralCrossRoots A strategy
      hwin hreachable incoming tag fallbackLeft fallbackRight _ rightAnchor
        leftAnchor hmatch).rightCrossPinned

/-- Strict-left mirror. -/
theorem tailStrictLeftConstructorCross_of_matchesLiteralCrossRoots
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    {state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial (CrossValid A strategy hwin)}
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial (CrossValid A strategy hwin) package.policy state)
    (incoming : In₁ × In₂)
    (tag : Tag A strategy hwin)
    (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂)
    (rightAnchor leftAnchor : Bool)
    (hmatch : package.TailNextMatchesLiteralCrossRoots A strategy hwin state
      incoming tag fallbackLeft fallbackRight
        (profiledRawJointHybridShadowPhaseLiveTailSwitchStrictLeftNext A
          strategy hwin tag fallbackLeft fallbackRight one two input)
        rightAnchor leftAnchor) :
    ProfiledRawJointHybridShadowPhaseLiveTailStrictLeftConstructorCross A
      strategy hwin tag fallbackLeft fallbackRight one two input := by
  apply
    profiledRawJointHybridShadowPhaseLiveTailStrictLeftConstructorCross_of_pinned
  exact
    (package.tailSuccessorPinnedToPair_of_matchesLiteralCrossRoots A strategy
      hwin hreachable incoming tag fallbackLeft fallbackRight _ rightAnchor
        leftAnchor hmatch).leftCrossPinned

/-- The simultaneous-close successor consumes the left-selected packet, just
as the existing Tail constructor audit requires. -/
theorem tailBothConstructorCross_of_matchesLiteralCrossRoots
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    {state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial (CrossValid A strategy hwin)}
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial (CrossValid A strategy hwin) package.policy state)
    (incoming : In₁ × In₂)
    (tag : Tag A strategy hwin)
    (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂)
    (rightAnchor leftAnchor : Bool)
    (hmatch : package.TailNextMatchesLiteralCrossRoots A strategy hwin state
      incoming tag fallbackLeft fallbackRight
        (profiledRawJointHybridShadowPhaseLiveTailSwitchBothNext A strategy
          hwin tag fallbackLeft fallbackRight one two input)
        rightAnchor leftAnchor) :
    ProfiledRawJointHybridShadowPhaseLiveTailBothConstructorCross A strategy
      hwin tag fallbackLeft fallbackRight one two input := by
  apply profiledRawJointHybridShadowPhaseLiveTailBothConstructorCross_of_pinned
  exact
    (package.tailSuccessorPinnedToPair_of_matchesLiteralCrossRoots A strategy
      hwin hreachable incoming tag fallbackLeft fallbackRight _ rightAnchor
        leftAnchor hmatch).leftCrossPinned

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
