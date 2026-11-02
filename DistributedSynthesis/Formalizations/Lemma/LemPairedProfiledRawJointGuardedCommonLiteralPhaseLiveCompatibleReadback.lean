/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatiblePathAcceptance
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralPhaseLiveStageFixedTailBookkeeping
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralPhaseLivePriorityReadback

/-!
# Compatible-path readback for the phase-live controller

The compatible hybrid rational policy exists unconditionally once a winning
strategy has been fixed.  This file selects that policy once, before the
environment is known, and exposes the exact remaining operational target:

* coherent compatible-table paths in the recurrent and persistent-reversal
  regimes; and
* the already isolated live-stage cuts in the two eventually fixed regimes.

Those data fill the ordinary four-regime physical acceptance record for the
actual rooted phase-live controller and hence `ReadbackUpgrade`.  In
particular, an environment is not allowed to select a fresh rational policy,
and no executable endpoint receives the policy, graph, orientation, hierarchy
side, leader bit, history, or view.
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

/-! ## One policy fixed before the environment -/

/-- The compatible hybrid policy selected once from the unconditional
parent-linked rationalization.  Its value may depend on the supplied winning
strategy, but not on the later environment. -/
noncomputable def literalCombinedFreshPhaseLiveCompatiblePolicy
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)) :
    CompatiblePolicy A strategy hwin :=
  Classical.choice
    (nonempty_profiledRawJointHybridPhysicalCompatibleRationalPolicy A
      strategy hwin (HybridInitial A strategy))

/-! ## Exact remaining operational package -/

/-- Strategy-indexed operational data for the positive compatible route.

The compatible policy is fixed by
`literalCombinedFreshPhaseLiveCompatiblePolicy` before `env` is quantified.
Only proof-side paths, physical cuts, and stage witnesses may depend on the
environment. -/
def PerStrategyWinningLiteralCombinedFreshPhaseLiveCompatibleBookkeeping :
    Prop :=
  ∀ (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (env : EnvironmentSequence In₁ In₂),
    let package := literalCombinedFreshPendingOnlyDefaultPackage A strategy
      hwin
    let controller :=
      package.literalCombinedFreshPhaseLiveRootPhysicalController A strategy
        hwin
    let policy := literalCombinedFreshPhaseLiveCompatiblePolicy A strategy
      hwin
    ProfiledRawJointGuardedCommonDecoratedPolicyPackage.LiteralCombinedFreshPhaseLivePhysicalCompatibleHardAlignments
        A strategy hwin package env policy ∧
      ProfiledRawJointGuardedCommonDecoratedPolicyPackage.LiteralCombinedFreshPhaseLiveStageFixedTailBookkeeping
        A strategy hwin package controller env

/-! ## Four regimes and readback -/

/-- Compatible hard paths plus the live-stage fixed tails supply physical
acceptance of the actual rooted phase-live controller for every environment. -/
theorem
    perStrategyWinningLiteralCombinedFreshPhaseLivePhysicalAcceptance_of_compatibleBookkeeping
    (hbookkeeping :
      PerStrategyWinningLiteralCombinedFreshPhaseLiveCompatibleBookkeeping A) :
    PerStrategyWinningLiteralCombinedFreshPhaseLivePhysicalAcceptance A := by
  intro strategy hwin
  dsimp only
  intro env
  let package := literalCombinedFreshPendingOnlyDefaultPackage A strategy hwin
  let controller :=
    package.literalCombinedFreshPhaseLiveRootPhysicalController A strategy
      hwin
  let policy := literalCombinedFreshPhaseLiveCompatiblePolicy A strategy hwin
  have hstrategy := hbookkeeping strategy hwin
  dsimp only at hstrategy
  have hdata := hstrategy env
  change
    ProfiledRawJointGuardedCommonDecoratedPolicyPackage.LiteralCombinedFreshPhaseLivePhysicalCompatibleHardAlignments
        A strategy hwin package env policy ∧
      ProfiledRawJointGuardedCommonDecoratedPolicyPackage.LiteralCombinedFreshPhaseLiveStageFixedTailBookkeeping
        A strategy hwin package controller env at hdata
  rcases hdata with ⟨hard, fixed⟩
  refine ⟨hard.physicalAcceptance A strategy hwin
    (fixed.fixedRight A strategy hwin)
    (fixed.fixedLeft A strategy hwin)⟩

/-- Final one-arrow local-summary extraction for the compatible operational
package. -/
theorem exists_readbackUpgrade_of_phaseLiveCompatibleBookkeeping
    (fallback : LocalSummaryAutomaton.{u, v,
      max (max (max (max s u) v) x) y} In₁ In₂)
    (hbookkeeping :
      PerStrategyWinningLiteralCombinedFreshPhaseLiveCompatibleBookkeeping A) :
    ∃ M : LocalSummaryAutomaton.{u, v,
        max (max (max (max s u) v) x) y} In₁ In₂,
      M.ReadbackUpgrade (Out₁ := Out₁) (Out₂ := Out₂) A := by
  exact exists_readbackUpgrade_of_phaseLivePhysicalAcceptance A fallback
    (perStrategyWinningLiteralCombinedFreshPhaseLivePhysicalAcceptance_of_compatibleBookkeeping
      A hbookkeeping)

end

end DetParityAutomaton

end DistributedSynthesis
