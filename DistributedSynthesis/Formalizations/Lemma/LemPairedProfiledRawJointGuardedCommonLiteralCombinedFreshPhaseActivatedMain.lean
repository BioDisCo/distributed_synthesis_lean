/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshPhaseActivatedReadback
import DistributedSynthesis.Formalizations.Lemma.LemStarSummaryHosting
import DistributedSynthesis.Formalizations.Theorem.ThmMainSummaryWinner

/-!
# Star and full-LTL endpoints for the phase-activated route

This file is only final composition.  Unconditional all-environment
acceptance of the finite phase-activated controller yields the finite summary
retraction, the star fold, direct DPA synthesis decidability, and the full LTL
main theorem.  No further certificate or literature premise occurs here.
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

/-- The activated finite controller supplies the complete star fold. -/
noncomputable def starFoldPackageOfPhaseActivatedAcceptance
    (fallback : LocalSummaryAutomaton.{u, u, u} In₁ In₂)
    (hactivated :
      PerStrategyWinningLiteralCombinedFreshPhaseActivatedAcceptance A) :
    StarFoldPackage A :=
  starFoldPackageOfExistsReadbackUpgrade A
    (exists_readbackUpgrade_of_phaseActivatedAcceptance A fallback hactivated)

/-- Direct DPA synthesis decidability through the constant star game. -/
noncomputable def synthesisDecidable_direct_of_phaseActivatedAcceptance
    (fallback : LocalSummaryAutomaton.{u, u, u} In₁ In₂)
    (hactivated :
      PerStrategyWinningLiteralCombinedFreshPhaseActivatedAcceptance A) :
    Decidable
      (∃ strategy : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          A.Accepts (execution strategy env)) := by
  classical
  exact
    (starFoldPackageOfPhaseActivatedAcceptance A fallback hactivated
      ).synthesisDecidable_direct

end

end DetParityAutomaton

/-! ## Canonically compiled LTL objective -/

/-- Full finite-alphabet LTL synthesis from unconditional acceptance of the
phase-activated controller constructed for every winning strategy. -/
noncomputable def
    main_result_for_ltl_full_synthesis_finiteAlphabets_of_phaseActivatedAcceptance
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
    (hactivated :
      DetParityAutomaton.PerStrategyWinningLiteralCombinedFreshPhaseActivatedAcceptance
        ((PositiveLTL.canonicalLTLToDPACompiler interp dec).compile formula)) :
    Decidable
      (∃ strategy : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          LTL.Satisfies interp (execution strategy env) formula) :=
  main_result_for_ltl_full_synthesis_finiteAlphabets_of_existsReadbackUpgrade
    In₁ In₂ Out₁ Out₂ interp dec formula
      (DetParityAutomaton.exists_readbackUpgrade_of_phaseActivatedAcceptance
        ((PositiveLTL.canonicalLTLToDPACompiler interp dec).compile formula)
        fallback hactivated)

end DistributedSynthesis
