/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshPendingOnlyTraceInstalledKey
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOperationalCloseCuts

/-!
# Installed literal key at an operational close

The operational graph clock cuts a strict homogeneous run immediately after
its final round and cuts a simultaneous round immediately after that singleton
round.  This file identifies the literal key installed by that exact closing
round with the corresponding letter of the already accepted installed-child
code word.

The statement is deliberately boundary-indexed.  It does not identify a
fresh child letter with every physical output inside a strict run: on a strict
round the nonreceiver keeps its old sender key.  Thus the result is compatible
with block-minimum pasting and does not introduce an executable orientation or
leader test.
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

/-- Exact post-round key behavior, uniformly packaged over the three graph
cases.  In all cases the receiver-side installed key names the code letter at
the same physical round. -/
structure LiteralCombinedFreshPendingOnlyInstalledKeyAt
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat) where
  one : OnePending A strategy hwin package
  two : TwoPending A strategy hwin package
  oneNext : OnePending A strategy hwin package
  twoNext : TwoPending A strategy hwin package
  controls_eq :
    package.literalCombinedFreshPendingOnlyTrace A strategy hwin
        (package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin)
        (package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin)
        env n =
      ((.inl one : OneControl A strategy hwin package),
        (.inl two : TwoControl A strategy hwin package))
  next_controls_eq :
    package.literalCombinedFreshPendingOnlyTrace A strategy hwin
        (package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin)
        (package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin)
        env (n + 1) =
      ((.inl oneNext : OneControl A strategy hwin package),
        (.inl twoNext : TwoControl A strategy hwin package))
  key_behavior :
    match (env n).graph with
    | .right =>
        oneNext.2.1.2.1.1 = one.2.1.2.1.1 ∧
        twoNext.2.1.2.1.1 =
          package.literalCombinedFreshPendingOnlyTraceFreshKey A strategy hwin
            env n
    | .left =>
        twoNext.2.1.2.1.1 = two.2.1.2.1.1 ∧
        oneNext.2.1.2.1.1 =
          package.literalCombinedFreshPendingOnlyTraceFreshKey A strategy hwin
            env n
    | .both =>
        oneNext.2.1.2.1.1 =
            package.literalCombinedFreshPendingOnlyTraceFreshKey A strategy
              hwin env n ∧
        twoNext.2.1.2.1.1 =
            package.literalCombinedFreshPendingOnlyTraceFreshKey A strategy
              hwin env n ∧
        oneNext.2.1.2.1.1 = twoNext.2.1.2.1.1
  installed_child_code :
    (package.literalRightSeamChildPoint A strategy hwin
      (package.literalCombinedFreshPendingOnlyTraceFreshKey A strategy hwin env
        n)).code A strategy =
      package.literalCombinedFreshPendingInstalledChildCodeWord A strategy
        hwin (literalCombinedFreshPendingOnlyTraceInputs env)
          (literalCombinedFreshPendingOnlyTraceGraphs env) n

/-- Every physical round has the exact installed-key witness.  The graph split
is proof-side only. -/
theorem literalCombinedFreshPendingOnlyTrace_installedKeyAt
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    Nonempty
      (LiteralCombinedFreshPendingOnlyInstalledKeyAt A strategy hwin package
        env n) := by
  cases hgraph : (env n).graph with
  | right =>
      rcases package.literalCombinedFreshPendingOnlyTrace_strictRight_keys A
        strategy hwin env n hgraph with
        ⟨one, two, oneNext, twoNext, hcontrols, hnext, hone, htwo, hcode⟩
      refine ⟨⟨one, two, oneNext, twoNext, hcontrols, hnext, ?_, ?_⟩⟩
      · simp only [hgraph]
        exact ⟨hone, htwo⟩
      · exact package.literalCombinedFreshPendingOnlyTraceFreshKey_childCode
          A strategy hwin env n
  | left =>
      rcases package.literalCombinedFreshPendingOnlyTrace_strictLeft_keys A
        strategy hwin env n hgraph with
        ⟨one, two, oneNext, twoNext, hcontrols, hnext, htwo, hone, hcode⟩
      refine ⟨⟨one, two, oneNext, twoNext, hcontrols, hnext, ?_, ?_⟩⟩
      · simp only [hgraph]
        exact ⟨htwo, hone⟩
      · exact package.literalCombinedFreshPendingOnlyTraceFreshKey_childCode
          A strategy hwin env n
  | both =>
      rcases package.literalCombinedFreshPendingOnlyTrace_both_keys A strategy
        hwin env n hgraph with
        ⟨one, two, oneNext, twoNext, hcontrols, hnext, hone, htwo, heq, hcode⟩
      refine ⟨⟨one, two, oneNext, twoNext, hcontrols, hnext, ?_, ?_⟩⟩
      · simp only [hgraph]
        exact ⟨hone, htwo, heq⟩
      · exact package.literalCombinedFreshPendingOnlyTraceFreshKey_childCode
          A strategy hwin env n

/-- Boundary-indexed version of the installed-key witness. -/
structure LiteralCombinedFreshPendingOnlyOperationalCloseInstalledKeyAt
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (k : Nat) where
  installed :
    LiteralCombinedFreshPendingOnlyInstalledKeyAt A strategy hwin package env
      (cuts.cuts (k + 1) - 1)
  closing_graph_eq :
    (env (cuts.cuts (k + 1) - 1)).graph = (env (cuts.cuts k)).graph

/-- At block `k`, the exact final physical round installs the fresh key naming
the accepted code letter at index `cuts (k+1)-1`; its graph is the graph that
opened the operational block. -/
theorem literalCombinedFreshPendingOnly_operationalClose_installedKeyAt
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (k : Nat) :
    Nonempty
      (LiteralCombinedFreshPendingOnlyOperationalCloseInstalledKeyAt A
        strategy hwin package env cuts k) := by
  rcases package.literalCombinedFreshPendingOnlyTrace_installedKeyAt A strategy
    hwin env (cuts.cuts (k + 1) - 1) with ⟨installed⟩
  exact ⟨⟨installed, cuts.closing_graph_eq k⟩⟩

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
