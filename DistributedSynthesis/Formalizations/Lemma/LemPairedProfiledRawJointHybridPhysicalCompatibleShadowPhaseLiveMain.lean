/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLivePhysicalAcceptance
import DistributedSynthesis.Formalizations.Lemma.LemStarSummaryHosting
import DistributedSynthesis.Formalizations.Theorem.ThmMainSummaryWinner

/-!
# Main-theorem endpoints for the delayed root-pinned phase-live route

This file is only final composition.  Once one finite physical controller is
constructed per winning distributed strategy and its delayed root-pinned tags
supply the hard-regime certificates, the policy-free physical-acceptance
adapter gives `ReadbackUpgrade`.  The existing star and full-synthesis
backends then apply without a common-root policy cast, a hierarchy oracle, or
another mathematical premise.
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

/-- Delayed root-pinned bookkeeping supplies the complete star fold. -/
noncomputable def starFoldPackageOfShadowPhaseLiveRootPinnedController
    (fallback : LocalSummaryAutomaton.{u, u, u} In₁ In₂)
    (hbookkeeping :
      PerStrategyWinningShadowPhaseLiveRootPinnedControllerBookkeeping.{u, u,
        u, u, u, u} A) :
    StarFoldPackage A :=
  starFoldPackageOfExistsReadbackUpgrade A
    (exists_readbackUpgrade_of_shadowPhaseLiveRootPinnedController A fallback
      hbookkeeping)

/-- Direct DPA synthesis decidability for the same finite controller. -/
noncomputable def
    synthesisDecidable_direct_of_shadowPhaseLiveRootPinnedController
    (fallback : LocalSummaryAutomaton.{u, u, u} In₁ In₂)
    (hbookkeeping :
      PerStrategyWinningShadowPhaseLiveRootPinnedControllerBookkeeping.{u, u,
        u, u, u, u} A) :
    Decidable
      (∃ strategy : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          A.Accepts (execution strategy env)) := by
  classical
  exact
    (starFoldPackageOfShadowPhaseLiveRootPinnedController A fallback
      hbookkeeping).synthesisDecidable_direct

end

end DetParityAutomaton

/-! ## Canonically compiled LTL objective -/

/-- Full finite-alphabet LTL synthesis from the delayed root-pinned
phase-live controller bookkeeping. -/
noncomputable def
    main_result_for_ltl_full_synthesis_finiteAlphabets_of_shadowPhaseLiveRootPinnedController
    {AP : Type}
    (In₁ In₂ Out₁ Out₂ : Type)
    [DecidableEq AP]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
    (interp : AP → RoundRecord In₁ In₂ Graph Out₁ Out₂ → Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (formula : LTL AP)
    [DecidableEq
      ((PositiveLTL.canonicalLTLToDPACompiler interp dec).compile
        formula).State]
    (fallback : LocalSummaryAutomaton.{0, 0, 0} In₁ In₂)
    (hbookkeeping :
      DetParityAutomaton.PerStrategyWinningShadowPhaseLiveRootPinnedControllerBookkeeping
        ((PositiveLTL.canonicalLTLToDPACompiler interp dec).compile formula)) :
    Decidable
      (∃ strategy : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          LTL.Satisfies interp (execution strategy env) formula) :=
  main_result_for_ltl_full_synthesis_finiteAlphabets_of_existsReadbackUpgrade
    In₁ In₂ Out₁ Out₂ interp dec formula
      (DetParityAutomaton.exists_readbackUpgrade_of_shadowPhaseLiveRootPinnedController
        ((PositiveLTL.canonicalLTLToDPACompiler interp dec).compile formula)
        fallback hbookkeeping)

end DistributedSynthesis
