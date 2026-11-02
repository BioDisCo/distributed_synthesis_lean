/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonDecoratedPolicyFreshnessCarrier
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossFreshStagedClose

/-!
# Freshness resolves the literal simultaneous close

This file joins the leader-free freshness carrier to the literal-cross
simultaneous-output theorem and the checked fresh staged close.  It is the
positive replacement for an invalid old-control/new-control equality:

* the receiving endpoints update the unique current finite policy copy;
* at `both` their copies are equal and name the preselected successor pair;
* the literal receiver roots emit that successor pair's physical record; and
* the fresh empty-prefix close installs the recurrent continuation for the
  very same pair.

No executable map below receives a graph, orientation, leader bit, semantic
history, or local view.  The graph occurs only in the proof-side product step.
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

private abbrev FreshOne :=
  ProfiledRawJointGuardedCommonDecoratedFreshnessOneState A strategy hwin
    initial

private abbrev FreshTwo :=
  ProfiledRawJointGuardedCommonDecoratedFreshnessTwoState A strategy hwin
    initial

/-! ## One checked resolve-select-emit-close step -/

/-- Starting from a retained right table, a simultaneous physical round uses
the unique fresh policy successor, emits its literal physical record, and
closes the same guarded pair at the checked empty prefix.

The conclusion deliberately contains no equality between the receiver state
before and after resolution.  Such an equality is neither needed nor true in
general: the next receive has already resolved the old pending bit. -/
theorem decoratedFreshness_both_rightLiteral_emit_close
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (one : FreshOne A strategy hwin) (two : FreshTwo A strategy hwin)
    (haligned : DecoratedFreshnessAligned A strategy hwin one two)
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial (CrossValid A strategy hwin) package.policy
          (decoratedFreshnessCurrent A strategy hwin one two))
    (incoming blockInput : In₁ × In₂) (anchor : Bool) :
    let state := decoratedFreshnessCurrent A strategy hwin one two
    let freshNext :=
      decoratedFreshnessLocalStep A strategy hwin package one two incoming
        .both
    let nextState :=
      decoratedFreshnessCurrent A strategy hwin freshNext.1 freshNext.2
    let initialState :=
      package.currentRightLiteralCrossMismatchInitial A strategy hwin
        nextState anchor
    let result :=
      profiledRawJointGuardedCommonLiteralCrossMismatchLocalStep A
        initialState.1 initialState.2 blockInput .both
    let pair := package.nextPairAt A strategy hwin state incoming
    let physical :=
      (pair.rightRootRecord A strategy hwin blockInput).2.1.physical
    (result.1.1, result.2.1) =
        (pairedRightClosingForRow .both physical,
          pairedRightInformedForRow .both physical) ∧
      package.pairAt A strategy hwin nextState = pair ∧
      (package.successorLiteralCrossFreshRightStagedClose A strategy hwin
          state incoming blockInput).handoff.1 = pair := by
  dsimp only
  have hstate :=
    decoratedFreshnessLocalStep_current_eq_successor A strategy hwin package
      one two haligned incoming .both
  have houtput :=
    package.currentRightLiteralCrossMismatchInitial_successor_bothOutput_eq_freshRightPhysical
      A strategy hwin hreachable incoming blockInput anchor
  have hpair :=
    decoratedFreshnessLocalStep_currentPair_eq_nextPairAt A strategy hwin
      package one two haligned incoming .both
  rw [hstate]
  exact ⟨houtput, hpair,
    package.successorLiteralCrossFreshRightStagedClose_pair A strategy hwin
      (decoratedFreshnessCurrent A strategy hwin one two) incoming
        blockInput⟩

/-- The same resolve-select-emit-close theorem when the retained carrier was
in its left phase.  The fixed right-close convention is proof-side only and
does not inspect the preceding phase. -/
theorem decoratedFreshness_both_leftLiteral_emit_close
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (one : FreshOne A strategy hwin) (two : FreshTwo A strategy hwin)
    (haligned : DecoratedFreshnessAligned A strategy hwin one two)
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial (CrossValid A strategy hwin) package.policy
          (decoratedFreshnessCurrent A strategy hwin one two))
    (incoming blockInput : In₁ × In₂) (anchor : Bool) :
    let state := decoratedFreshnessCurrent A strategy hwin one two
    let freshNext :=
      decoratedFreshnessLocalStep A strategy hwin package one two incoming
        .both
    let nextState :=
      decoratedFreshnessCurrent A strategy hwin freshNext.1 freshNext.2
    let initialState :=
      package.currentLeftLiteralCrossMismatchInitial A strategy hwin
        nextState anchor
    let result :=
      profiledRawJointGuardedCommonLiteralCrossMismatchLocalStep A
        initialState.1 initialState.2 blockInput .both
    let pair := package.nextPairAt A strategy hwin state incoming
    let physical :=
      (pair.rightRootRecord A strategy hwin blockInput).2.1.physical
    (result.1.1, result.2.1) =
        (pairedRightClosingForRow .both physical,
          pairedRightInformedForRow .both physical) ∧
      package.pairAt A strategy hwin nextState = pair ∧
      (package.successorLiteralCrossFreshRightStagedClose A strategy hwin
          state incoming blockInput).handoff.1 = pair := by
  dsimp only
  have hstate :=
    decoratedFreshnessLocalStep_current_eq_successor A strategy hwin package
      one two haligned incoming .both
  have houtput :=
    package.currentLeftLiteralCrossMismatchInitial_successor_bothOutput_eq_freshRightPhysical
      A strategy hwin hreachable incoming blockInput anchor
  have hpair :=
    decoratedFreshnessLocalStep_currentPair_eq_nextPairAt A strategy hwin
      package one two haligned incoming .both
  rw [hstate]
  exact ⟨houtput, hpair,
    package.successorLiteralCrossFreshRightStagedClose_pair A strategy hwin
      (decoratedFreshnessCurrent A strategy hwin one two) incoming
        blockInput⟩

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
