/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingDeferredMemberControl
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralRightPendingForkCoherence
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralLeftDeferredStageFork

/-!
# Repacking the two literal pending seams into the generic deferred carrier

The concrete tables store a dependent seam key outside their member bit,
whereas `DeferredMemberControl` stores the bit first.  This file proves that
the difference is only a finite repacking: both concrete no-receive maps and
both canonical pending forks commute with the generic equivalence.

These are proof adapters only.  They do not add a phase selector or change
the executable maps.  In particular, no graph, orientation, hierarchy side,
leader bit, strict-leader bit, history, or view is supplied to a transition.
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

private abbrev Package (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy hwin initial
    (CrossValid A strategy hwin)

private abbrev RightKey
    (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin package

private abbrev RightInstalled
    (package : Package A strategy hwin initial)
    (key : RightKey A strategy hwin package) :=
  package.literalRightSeamInstalled A strategy hwin key

private abbrev RightSharedAt
    (package : Package A strategy hwin initial)
    (key : RightKey A strategy hwin package) :=
  ProfiledRawJointLiteralRightBothExactSenderState A strategy hwin
    (RightInstalled A strategy hwin package key)

private abbrev RightShared
    (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamStagedSenderState A strategy
    hwin package

private abbrev RightStage
    (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamStage A strategy hwin package

private abbrev RightPending
    (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamPendingSenderCandidate A
    strategy hwin package

private abbrev LeftKey
    (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin package

private abbrev LeftInstalled
    (package : Package A strategy hwin initial)
    (key : LeftKey A strategy hwin package) :=
  package.literalLeftSeamInstalled A strategy hwin key

private abbrev LeftSharedAt
    (package : Package A strategy hwin initial)
    (key : LeftKey A strategy hwin package) :=
  ProfiledRawJointLiteralLeftBothExactSenderState A strategy hwin
    (LeftInstalled A strategy hwin package key)

private abbrev LeftShared
    (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralLeftSeamStagedSenderState A strategy hwin
    package

private abbrev LeftStage
    (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralLeftSeamStage A strategy hwin package

private abbrev LeftPending
    (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralLeftSeamDeferredSenderCandidate A
    strategy hwin package

/-! ## Right seam -/

/-- The existing right pending carrier is exactly the generic carrier after
dependent-key repacking. -/
def literalRightSeamPendingEquiv
    (package : Package A strategy hwin initial) :
    RightPending A strategy hwin package ≃
      FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
        (RightShared A strategy hwin package)
        (Option (RightStage A strategy hwin package)) :=
  FiniteAcknowledgedDelayedCarrier.keyedDeferredMemberEquiv

/-- Repacking commutes with the concrete right pending no-receive. -/
theorem literalRightSeamPendingNoRecv_repack
    (package : Package A strategy hwin initial)
    (state : RightPending A strategy hwin package) (input : In₂) :
    (package.literalRightSeamPendingEquiv A strategy hwin
        (package.literalRightSeamPendingSenderNoRecv A strategy hwin state
          input).1,
      (package.literalRightSeamPendingSenderNoRecv A strategy hwin state
        input).2) =
      FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
        (package.literalRightSeamDeferredSharedStep A strategy hwin)
        (package.literalRightSeamPendingEquiv A strategy hwin state) input := by
  rcases state with ⟨⟨key, member, shared⟩, stage⟩
  rfl

/-- The concrete right pending fork is the generic canonical fork after
repacking both candidates. -/
theorem literalRightSeamPendingFork_repack
    (package : Package A strategy hwin initial)
    (key : RightKey A strategy hwin package)
    (shared : RightSharedAt A strategy hwin package key)
    (stage : Option (RightStage A strategy hwin package)) :
    let concrete := package.literalRightSeamPendingSenderFork A strategy hwin
      key shared stage
    (FiniteDelayedFork.mk
        (package.literalRightSeamPendingEquiv A strategy hwin
          concrete.openControl)
        (package.literalRightSeamPendingEquiv A strategy hwin
          concrete.closedControl)) =
      FiniteAcknowledgedDelayedCarrier.deferredMemberFork
        (⟨key, shared⟩ : RightShared A strategy hwin package) stage := by
  rfl

/-! ## Left seam -/

/-- The existing left deferred carrier is the same generic carrier after
dependent-key repacking. -/
def literalLeftSeamDeferredEquiv
    (package : Package A strategy hwin initial) :
    LeftPending A strategy hwin package ≃
      FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
        (LeftShared A strategy hwin package)
        (Option (LeftStage A strategy hwin package)) :=
  FiniteAcknowledgedDelayedCarrier.keyedDeferredMemberEquiv

/-- Repacking commutes with the concrete left deferred no-receive. -/
theorem literalLeftSeamDeferredNoRecv_repack
    (package : Package A strategy hwin initial)
    (state : LeftPending A strategy hwin package) (input : In₁) :
    (package.literalLeftSeamDeferredEquiv A strategy hwin
        (package.literalLeftSeamDeferredSenderNoRecv A strategy hwin state
          input).1,
      (package.literalLeftSeamDeferredSenderNoRecv A strategy hwin state
        input).2) =
      FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
        (package.literalLeftSeamDeferredSharedStep A strategy hwin)
        (package.literalLeftSeamDeferredEquiv A strategy hwin state) input := by
  rcases state with ⟨⟨key, member, shared⟩, stage⟩
  rfl

/-- The concrete left pending fork is the generic canonical fork after
repacking both candidates. -/
theorem literalLeftSeamDeferredFork_repack
    (package : Package A strategy hwin initial)
    (key : LeftKey A strategy hwin package)
    (shared : LeftSharedAt A strategy hwin package key)
    (stage : Option (LeftStage A strategy hwin package)) :
    let concrete := package.literalLeftSeamDeferredSenderFork A strategy hwin
      key shared stage
    (FiniteDelayedFork.mk
        (package.literalLeftSeamDeferredEquiv A strategy hwin
          concrete.openControl)
        (package.literalLeftSeamDeferredEquiv A strategy hwin
          concrete.closedControl)) =
      FiniteAcknowledgedDelayedCarrier.deferredMemberFork
        (⟨key, shared⟩ : LeftShared A strategy hwin package) stage := by
  rfl

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
