/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshPendingOnlyTraceFreshnessAlignment

/-!
# Installed literal keys along the pending-only trace

The accepted common-code word and the finite physical controller use the
same leader-free freshness path.  This file records the exact operational
consequence at one physical round.  A receiving endpoint installs the fresh
literal key named by the accepted letter at that round.  In a strict round,
the nonreceiving endpoint instead advances its old sender table and retains
its old key.  In a simultaneous round both new sender tables carry the same
fresh key.

This is intentionally a key law rather than a pointwise code/physical-word
equation.  It exposes the honest epoch boundaries needed by block-minimum
pasting and does not pretend that the simultaneous-tree code clock is the
physical round clock.
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

private abbrev Key (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin package

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

/-! ## The exact fresh key named by the accepted letter -/

/-- The proof-side fresh literal key selected before physical round `n`. -/
noncomputable def literalCombinedFreshPendingOnlyTraceFreshKey
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    Key A strategy hwin package :=
  let current := package.literalCombinedFreshPendingFreshnessTrace A strategy
    hwin (literalCombinedFreshPendingOnlyTraceInputs env)
      (literalCombinedFreshPendingOnlyTraceGraphs env) n
  package.literalRightSeamFreshKey A strategy hwin
    (decoratedFreshnessCurrent A strategy hwin current.1 current.2)
    (literalCombinedFreshPendingOnlyTraceInputs env n)

/-- The accepted installed-child letter is literally the incidence code of
the occurrence at `TraceFreshKey`. -/
@[simp] theorem literalCombinedFreshPendingOnlyTraceFreshKey_childCode
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    (package.literalRightSeamChildPoint A strategy hwin
      (package.literalCombinedFreshPendingOnlyTraceFreshKey A strategy hwin env
        n)).code A strategy =
      package.literalCombinedFreshPendingInstalledChildCodeWord A strategy hwin
        (literalCombinedFreshPendingOnlyTraceInputs env)
        (literalCombinedFreshPendingOnlyTraceGraphs env) n :=
  rfl

/-- The trace key is the concrete common boundary key computed from the two
pending shared states before round `n`. -/
theorem literalCombinedFreshPendingOnlyTraceFreshKey_eq_boundaryKey
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    let snapshot := package.literalCombinedFreshPendingOnlyTrace_freshnessAt A
      strategy hwin env n
    package.literalCombinedFreshPendingOnlyTraceFreshKey A strategy hwin env
        n =
      package.literalCombinedFreshPendingBoundaryKey A strategy hwin
        snapshot.one.2.1 snapshot.two.2.1
        (literalCombinedFreshPendingOnlyTraceInputs env n) := by
  dsimp only
  let snapshot := package.literalCombinedFreshPendingOnlyTrace_freshnessAt A
    strategy hwin env n
  have hfresh := snapshot.freshness_eq
  unfold literalCombinedFreshPendingOnlyTraceFreshKey
  rw [← hfresh]
  rfl

/-! ## The three physical graph cases -/

/-- On a strict-right round, process one advances its old left sender without
changing its key, while receiving process two installs exactly the fresh key
named by the accepted code letter. -/
theorem literalCombinedFreshPendingOnlyTrace_strictRight_keys
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hgraph : (env n).graph = .right) :
    ∃ (one : OnePending A strategy hwin package)
      (two : TwoPending A strategy hwin package)
      (oneNext : OnePending A strategy hwin package)
      (twoNext : TwoPending A strategy hwin package),
      package.literalCombinedFreshPendingOnlyTrace A strategy hwin
          (package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin)
          (package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin)
          env n =
        ((.inl one : OneControl A strategy hwin package),
          (.inl two : TwoControl A strategy hwin package)) ∧
      package.literalCombinedFreshPendingOnlyTrace A strategy hwin
          (package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin)
          (package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin)
          env (n + 1) =
        ((.inl oneNext : OneControl A strategy hwin package),
          (.inl twoNext : TwoControl A strategy hwin package)) ∧
      oneNext.2.1.2.1.1 = one.2.1.2.1.1 ∧
      twoNext.2.1.2.1.1 =
        package.literalCombinedFreshPendingOnlyTraceFreshKey A strategy hwin
          env n ∧
      (package.literalRightSeamChildPoint A strategy hwin
        twoNext.2.1.2.1.1).code A strategy =
        package.literalCombinedFreshPendingInstalledChildCodeWord A strategy
          hwin (literalCombinedFreshPendingOnlyTraceInputs env)
            (literalCombinedFreshPendingOnlyTraceGraphs env) n := by
  let snapshot := package.literalCombinedFreshPendingOnlyTrace_freshnessAt A
    strategy hwin env n
  let oneNext : OnePending A strategy hwin package :=
    (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
      (package.literalCombinedFreshOnePendingStep A strategy hwin)
      snapshot.one (env n).inputOne).1
  let twoShared := package.literalCombinedFreshTwoReceiveShared A strategy hwin
    snapshot.two.2.1 (env n).inputTwo snapshot.one.2.1 (env n).inputOne
  let twoNext : TwoPending A strategy hwin package :=
    (false, twoShared, none)
  have halignedTrace :=
    package.literalCombinedFreshPendingFreshnessTrace_aligned A strategy hwin
      (literalCombinedFreshPendingOnlyTraceInputs env)
      (literalCombinedFreshPendingOnlyTraceGraphs env) n
  have hone : snapshot.one.2.1.1 =
      (package.literalCombinedFreshPendingFreshnessTrace A strategy hwin
        (literalCombinedFreshPendingOnlyTraceInputs env)
        (literalCombinedFreshPendingOnlyTraceGraphs env) n).1 := by
    simpa only [Prod.fst] using congrArg Prod.fst snapshot.freshness_eq
  have htwo : snapshot.two.2.1.1 =
      (package.literalCombinedFreshPendingFreshnessTrace A strategy hwin
        (literalCombinedFreshPendingOnlyTraceInputs env)
        (literalCombinedFreshPendingOnlyTraceGraphs env) n).2 := by
    simpa only [Prod.snd] using congrArg Prod.snd snapshot.freshness_eq
  have haligned : DecoratedFreshnessAligned A strategy hwin
      snapshot.one.2.1.1 snapshot.two.2.1.1 := by
    rw [hone, htwo]
    exact halignedTrace
  have htwoKey : twoNext.2.1.2.1.1 =
      package.literalCombinedFreshPendingOnlyTraceFreshKey A strategy hwin env
        n := by
    dsimp only [twoNext, twoShared]
    rw [package.literalCombinedFreshTwoReceiveShared_sender_key A strategy
      hwin]
    rw [package.literalCombinedFreshTwoReceiveSource_eq_boundary_of_aligned A
      strategy hwin snapshot.one.2.1 snapshot.two.2.1 haligned]
    simpa [literalCombinedFreshPendingOnlyTraceInputs] using
      (package.literalCombinedFreshPendingOnlyTraceFreshKey_eq_boundaryKey A
        strategy hwin env n).symm
  refine ⟨snapshot.one, snapshot.two, oneNext, twoNext,
    snapshot.controls_eq, ?_, ?_, ?_, ?_⟩
  · have hcontrols := snapshot.controls_eq
    unfold literalCombinedFreshPendingOnlyTrace at hcontrols ⊢
    rw [FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
      hcontrols, hgraph]
    rfl
  · dsimp only [oneNext]
    exact package.literalLeftSeamFrontSenderNoRecv_key A strategy hwin
      snapshot.one.2.1.2.1 (env n).inputOne
  · exact htwoKey
  · rw [htwoKey]
    exact package.literalCombinedFreshPendingOnlyTraceFreshKey_childCode A
      strategy hwin env n

/-- Strict-left mirror: process two's old right sender keeps its key and
receiving process one installs the accepted fresh literal key. -/
theorem literalCombinedFreshPendingOnlyTrace_strictLeft_keys
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hgraph : (env n).graph = .left) :
    ∃ (one : OnePending A strategy hwin package)
      (two : TwoPending A strategy hwin package)
      (oneNext : OnePending A strategy hwin package)
      (twoNext : TwoPending A strategy hwin package),
      package.literalCombinedFreshPendingOnlyTrace A strategy hwin
          (package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin)
          (package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin)
          env n =
        ((.inl one : OneControl A strategy hwin package),
          (.inl two : TwoControl A strategy hwin package)) ∧
      package.literalCombinedFreshPendingOnlyTrace A strategy hwin
          (package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin)
          (package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin)
          env (n + 1) =
        ((.inl oneNext : OneControl A strategy hwin package),
          (.inl twoNext : TwoControl A strategy hwin package)) ∧
      twoNext.2.1.2.1.1 = two.2.1.2.1.1 ∧
      oneNext.2.1.2.1.1 =
        package.literalCombinedFreshPendingOnlyTraceFreshKey A strategy hwin
          env n ∧
      (package.literalRightSeamChildPoint A strategy hwin
        oneNext.2.1.2.1.1).code A strategy =
        package.literalCombinedFreshPendingInstalledChildCodeWord A strategy
          hwin (literalCombinedFreshPendingOnlyTraceInputs env)
            (literalCombinedFreshPendingOnlyTraceGraphs env) n := by
  let snapshot := package.literalCombinedFreshPendingOnlyTrace_freshnessAt A
    strategy hwin env n
  let oneShared := package.literalCrossCombinedFreshOneSharedAt A strategy hwin
    (package.literalCombinedFreshOneReceiveFreshness A strategy hwin
      snapshot.one.2.1 (env n).inputOne snapshot.two.2.1 (env n).inputTwo)
    (package.literalCombinedFreshOneReceiveKey A strategy hwin
      snapshot.one.2.1 (env n).inputOne snapshot.two.2.1 (env n).inputTwo)
  let oneNext : OnePending A strategy hwin package :=
    (false, oneShared, none)
  let twoNext : TwoPending A strategy hwin package :=
    (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
      (package.literalCombinedFreshTwoPendingStep A strategy hwin)
      snapshot.two (env n).inputTwo).1
  have honeKey : oneNext.2.1.2.1.1 =
      package.literalCombinedFreshPendingOnlyTraceFreshKey A strategy hwin env
        n := by
    dsimp only [oneNext, oneShared]
    simpa [literalCombinedFreshPendingOnlyTraceInputs] using
      (package.literalCombinedFreshPendingOnlyTraceFreshKey_eq_boundaryKey A
        strategy hwin env n).symm
  refine ⟨snapshot.one, snapshot.two, oneNext, twoNext,
    snapshot.controls_eq, ?_, ?_, ?_, ?_⟩
  · have hcontrols := snapshot.controls_eq
    unfold literalCombinedFreshPendingOnlyTrace at hcontrols ⊢
    rw [FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
      hcontrols, hgraph]
    rfl
  · dsimp only [twoNext]
    exact package.literalRightSeamFrontSenderNoRecv_key A strategy hwin
      snapshot.two.2.1.2.1 (env n).inputTwo
  · exact honeKey
  · rw [honeKey]
    exact package.literalCombinedFreshPendingOnlyTraceFreshKey_childCode A
      strategy hwin env n

/-- On a simultaneous receive, both endpoint-local fresh constructors install
the same accepted literal key. -/
theorem literalCombinedFreshPendingOnlyTrace_both_keys
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hgraph : (env n).graph = .both) :
    ∃ (one : OnePending A strategy hwin package)
      (two : TwoPending A strategy hwin package)
      (oneNext : OnePending A strategy hwin package)
      (twoNext : TwoPending A strategy hwin package),
      package.literalCombinedFreshPendingOnlyTrace A strategy hwin
          (package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin)
          (package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin)
          env n =
        ((.inl one : OneControl A strategy hwin package),
          (.inl two : TwoControl A strategy hwin package)) ∧
      package.literalCombinedFreshPendingOnlyTrace A strategy hwin
          (package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin)
          (package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin)
          env (n + 1) =
        ((.inl oneNext : OneControl A strategy hwin package),
          (.inl twoNext : TwoControl A strategy hwin package)) ∧
      oneNext.2.1.2.1.1 =
        package.literalCombinedFreshPendingOnlyTraceFreshKey A strategy hwin
          env n ∧
      twoNext.2.1.2.1.1 =
        package.literalCombinedFreshPendingOnlyTraceFreshKey A strategy hwin
          env n ∧
      oneNext.2.1.2.1.1 = twoNext.2.1.2.1.1 ∧
      (package.literalRightSeamChildPoint A strategy hwin
        oneNext.2.1.2.1.1).code A strategy =
        package.literalCombinedFreshPendingInstalledChildCodeWord A strategy
          hwin (literalCombinedFreshPendingOnlyTraceInputs env)
            (literalCombinedFreshPendingOnlyTraceGraphs env) n := by
  let snapshot := package.literalCombinedFreshPendingOnlyTrace_freshnessAt A
    strategy hwin env n
  let oneShared := package.literalCrossCombinedFreshOneSharedAt A strategy hwin
    (package.literalCombinedFreshOneReceiveFreshness A strategy hwin
      snapshot.one.2.1 (env n).inputOne snapshot.two.2.1 (env n).inputTwo)
    (package.literalCombinedFreshOneReceiveKey A strategy hwin
      snapshot.one.2.1 (env n).inputOne snapshot.two.2.1 (env n).inputTwo)
  let twoShared := package.literalCombinedFreshTwoReceiveShared A strategy hwin
    snapshot.two.2.1 (env n).inputTwo snapshot.one.2.1 (env n).inputOne
  let oneNext : OnePending A strategy hwin package :=
    (true, oneShared, none)
  let twoNext : TwoPending A strategy hwin package :=
    (true, twoShared, none)
  have halignedTrace :=
    package.literalCombinedFreshPendingFreshnessTrace_aligned A strategy hwin
      (literalCombinedFreshPendingOnlyTraceInputs env)
      (literalCombinedFreshPendingOnlyTraceGraphs env) n
  have hone : snapshot.one.2.1.1 =
      (package.literalCombinedFreshPendingFreshnessTrace A strategy hwin
        (literalCombinedFreshPendingOnlyTraceInputs env)
        (literalCombinedFreshPendingOnlyTraceGraphs env) n).1 := by
    simpa only [Prod.fst] using congrArg Prod.fst snapshot.freshness_eq
  have htwo : snapshot.two.2.1.1 =
      (package.literalCombinedFreshPendingFreshnessTrace A strategy hwin
        (literalCombinedFreshPendingOnlyTraceInputs env)
        (literalCombinedFreshPendingOnlyTraceGraphs env) n).2 := by
    simpa only [Prod.snd] using congrArg Prod.snd snapshot.freshness_eq
  have haligned : DecoratedFreshnessAligned A strategy hwin
      snapshot.one.2.1.1 snapshot.two.2.1.1 := by
    rw [hone, htwo]
    exact halignedTrace
  have honeKey : oneNext.2.1.2.1.1 =
      package.literalCombinedFreshPendingOnlyTraceFreshKey A strategy hwin env
        n := by
    dsimp only [oneNext, oneShared]
    simpa [literalCombinedFreshPendingOnlyTraceInputs] using
      (package.literalCombinedFreshPendingOnlyTraceFreshKey_eq_boundaryKey A
        strategy hwin env n).symm
  have htwoKey : twoNext.2.1.2.1.1 =
      package.literalCombinedFreshPendingOnlyTraceFreshKey A strategy hwin env
        n := by
    dsimp only [twoNext, twoShared]
    rw [package.literalCombinedFreshTwoReceiveShared_sender_key A strategy
      hwin]
    rw [package.literalCombinedFreshTwoReceiveSource_eq_boundary_of_aligned A
      strategy hwin snapshot.one.2.1 snapshot.two.2.1 haligned]
    simpa [literalCombinedFreshPendingOnlyTraceInputs] using
      (package.literalCombinedFreshPendingOnlyTraceFreshKey_eq_boundaryKey A
        strategy hwin env n).symm
  refine ⟨snapshot.one, snapshot.two, oneNext, twoNext,
    snapshot.controls_eq, ?_, honeKey, htwoKey, ?_, ?_⟩
  · have hcontrols := snapshot.controls_eq
    unfold literalCombinedFreshPendingOnlyTrace at hcontrols ⊢
    rw [FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
      hcontrols, hgraph]
    rfl
  · exact honeKey.trans htwoKey.symm
  · rw [honeKey]
    exact package.literalCombinedFreshPendingOnlyTraceFreshKey_childCode A
      strategy hwin env n

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
