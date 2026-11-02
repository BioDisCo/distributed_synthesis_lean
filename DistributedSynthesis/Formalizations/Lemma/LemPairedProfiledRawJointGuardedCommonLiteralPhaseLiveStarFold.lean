/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralPhaseLivePriorityReadback
import DistributedSynthesis.Formalizations.Lemma.LemStarSummaryHosting

/-!
# Star fold from phase-live priority acceptance

This is the paper-facing endpoint of the positive controller construction.
For one realizable DPA, the phase-live priority proof produces an existential
finite local-summary `ReadbackUpgrade`; the already proved summary hosting
then produces the complete `StarFoldPackage` and the direct constant-star-game
decision procedure.

The only premise below is the concrete four-regime priority property of the
fixed phase-live physical controller.  In particular there is no
`StarFoldCertificate`, journal extraction, fringe quotient, physically
activated pending/recurrent relay, or literature theorem left as a separate
hypothesis.
-/

namespace DistributedSynthesis

universe u

namespace DetParityAutomaton

variable {In₁ In₂ Out₁ Out₂ : Type u}
variable
  (A : DetParityAutomaton.{u, u}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-- The concrete phase-live priority construction supplies the star fold in
one arrow. -/
noncomputable def starFoldPackageOfPhaseLivePriorityAcceptance
    (fallback : LocalSummaryAutomaton.{u, u, u} In₁ In₂)
    (hphase :
      PerStrategyWinningLiteralCombinedFreshPhaseLivePriorityAcceptance A) :
    StarFoldPackage A :=
  starFoldPackageOfExistsReadbackUpgrade A
    (exists_readbackUpgrade_of_phaseLivePriorityAcceptance A fallback hphase)

/-- Anchor-free star fold from the standard physical-acceptance package
produced by the carried whole-block coupling. -/
noncomputable def starFoldPackageOfPhaseLivePhysicalAcceptance
    (fallback : LocalSummaryAutomaton.{u, u, u} In₁ In₂)
    (hphase :
      PerStrategyWinningLiteralCombinedFreshPhaseLivePhysicalAcceptance A) :
    StarFoldPackage A :=
  starFoldPackageOfExistsReadbackUpgrade A
    (exists_readbackUpgrade_of_phaseLivePhysicalAcceptance A fallback hphase)

/-- Direct DPA synthesis decidability through the constant-observation star
game, specialized to the phase-live controller construction. -/
noncomputable def synthesisDecidable_direct_of_phaseLivePriorityAcceptance
    (fallback : LocalSummaryAutomaton.{u, u, u} In₁ In₂)
    (hphase :
      PerStrategyWinningLiteralCombinedFreshPhaseLivePriorityAcceptance A) :
    Decidable
      (∃ strategy : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          A.Accepts (execution strategy env)) := by
  classical
  exact
    (starFoldPackageOfPhaseLivePriorityAcceptance A fallback hphase
      ).synthesisDecidable_direct

/-- Direct DPA synthesis decidability from the anchor-free carried physical
acceptance endpoint. -/
noncomputable def synthesisDecidable_direct_of_phaseLivePhysicalAcceptance
    (fallback : LocalSummaryAutomaton.{u, u, u} In₁ In₂)
    (hphase :
      PerStrategyWinningLiteralCombinedFreshPhaseLivePhysicalAcceptance A) :
    Decidable
      (∃ strategy : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          A.Accepts (execution strategy env)) := by
  classical
  exact
    (starFoldPackageOfPhaseLivePhysicalAcceptance A fallback hphase
      ).synthesisDecidable_direct

end


end DetParityAutomaton

end DistributedSynthesis
