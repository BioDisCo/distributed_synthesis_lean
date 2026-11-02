/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorResolvedMemberStream
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorCarrierReadback

/-!
# Readback from resolved-member packet streams

The operational trace proof naturally produces a resolved boundary stream,
whereas the existing readback endpoint consumes a successor-carrier tail.
This file performs exactly that erasure in the recurrent-synchronization and
persistent-reversal regimes.  Fixed strict tails continue to use the already
proved phase-live bookkeeping.
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

private abbrev DefaultInitial
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂) :=
  literalCombinedFreshPendingOnlyDefaultInitial A strategy

private abbrev HybridInitial
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂) :=
  (DefaultInitial A strategy).world A strategy

private abbrev CompatiblePolicy
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)) :=
  ProfiledRawJointHybridPhysicalCompatibleRationalPolicy A strategy hwin
    (HybridInitial A strategy)

private abbrev DefaultPackage
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)) :=
  literalCombinedFreshPendingOnlyDefaultPackage A strategy hwin

private abbrev PhaseLiveController
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)) :=
  (DefaultPackage A strategy hwin
    ).literalCombinedFreshPhaseLiveRootPhysicalController A strategy hwin

private abbrev ResolvedStream
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (policy : CompatiblePolicy A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) :=
  ProfiledRawJointHybridPhysicalCompatibleResolvedMemberStream A strategy hwin
    policy
      (PhaseLiveController A strategy hwin).globalMachine
      (PhaseLiveController A strategy hwin).globalOutputOne
      (PhaseLiveController A strategy hwin).globalOutputTwo env

/-- Exact trace-level output still required from the concrete delayed
controller for one environment. -/
structure LiteralCombinedFreshPhaseLiveResolvedMemberStreamBookkeeping
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (env : EnvironmentSequence In₁ In₂)
    (policy : CompatiblePolicy A strategy hwin) : Prop where
  recurrent : GraphBothRecurrent (fun n ↦ (env n).graph) →
    Nonempty (ResolvedStream A strategy hwin policy env)
  reversal : PersistentStrictReversalTail (fun n ↦ (env n).graph) →
    Nonempty (ResolvedStream A strategy hwin policy env)
  fixed :
    ProfiledRawJointGuardedCommonDecoratedPolicyPackage.LiteralCombinedFreshPhaseLiveStageFixedTailBookkeeping
      A strategy hwin (DefaultPackage A strategy hwin)
        (PhaseLiveController A strategy hwin) env

namespace LiteralCombinedFreshPhaseLiveResolvedMemberStreamBookkeeping

variable {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
variable {hwin : ∀ env : EnvironmentSequence In₁ In₂,
  A.Accepts (execution strategy env)}
variable {env : EnvironmentSequence In₁ In₂}
variable {policy : CompatiblePolicy A strategy hwin}

/-- Erase the packet-stream presentation and obtain the carrier bookkeeping
consumed by the existing readback theorem. -/
noncomputable def toCompatibleSuccessorCarrier
    (bookkeeping :
      LiteralCombinedFreshPhaseLiveResolvedMemberStreamBookkeeping A strategy
        hwin env policy) :
    LiteralCombinedFreshPhaseLiveCompatibleSuccessorCarrierBookkeeping A
      strategy hwin env policy where
  recurrent hboth := by
    let stream := Classical.choice (bookkeeping.recurrent hboth)
    exact ⟨stream.toCarrierCutTail A strategy hwin⟩
  reversal hreversal := by
    let stream := Classical.choice (bookkeeping.reversal hreversal)
    exact ⟨stream.toCarrierCutTail A strategy hwin⟩
  fixed := bookkeeping.fixed

end LiteralCombinedFreshPhaseLiveResolvedMemberStreamBookkeeping

/-- Strategy-indexed resolved streams are the precise remaining trace
obligation. -/
def PerStrategyWinningLiteralCombinedFreshPhaseLiveResolvedMemberStreamBookkeeping :
    Prop :=
  ∀ (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (env : EnvironmentSequence In₁ In₂),
    LiteralCombinedFreshPhaseLiveResolvedMemberStreamBookkeeping A strategy
      hwin env (literalCombinedFreshPhaseLiveCompatiblePolicy A strategy hwin)

/-- Resolved streams immediately discharge the carrier premise. -/
theorem
    perStrategyWinningCompatibleSuccessorCarrier_of_resolvedMemberStreams
    (hstream :
      PerStrategyWinningLiteralCombinedFreshPhaseLiveResolvedMemberStreamBookkeeping
        A) :
    PerStrategyWinningLiteralCombinedFreshPhaseLiveCompatibleSuccessorCarrierBookkeeping
      A := by
  intro strategy hwin env
  exact (hstream strategy hwin env).toCompatibleSuccessorCarrier A

/-- One-arrow finite-summary extraction from resolved member streams. -/
theorem exists_readbackUpgrade_of_resolvedMemberStreams
    (fallback : LocalSummaryAutomaton.{u, v,
      max (max (max (max s u) v) x) y} In₁ In₂)
    (hstream :
      PerStrategyWinningLiteralCombinedFreshPhaseLiveResolvedMemberStreamBookkeeping
        A) :
    ∃ M : LocalSummaryAutomaton.{u, v,
        max (max (max (max s u) v) x) y} In₁ In₂,
      M.ReadbackUpgrade (Out₁ := Out₁) (Out₂ := Out₂) A := by
  exact exists_readbackUpgrade_of_phaseLiveCompatibleSuccessorCarrier A
    fallback
      (perStrategyWinningCompatibleSuccessorCarrier_of_resolvedMemberStreams A
        hstream)

end


end DetParityAutomaton

end DistributedSynthesis
