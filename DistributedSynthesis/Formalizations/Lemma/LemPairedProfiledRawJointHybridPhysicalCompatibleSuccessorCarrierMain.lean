/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorCarrierReadback
import DistributedSynthesis.Formalizations.Lemma.LemStarSummaryHosting
import DistributedSynthesis.Formalizations.Theorem.ThmMainSummaryWinner

/-!
# Star and full-LTL endpoints for compatible successor carriers

This file is final composition only.  Per-strategy carrier bookkeeping for the
two hard graph regimes, together with the already proved fixed-tail cases,
gives `ReadbackUpgrade`; the existing star and main-theorem adapters then apply
without any further mathematical premise.
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

/-- Compatible successor-carrier bookkeeping supplies the complete star fold. -/
noncomputable def starFoldPackageOfCompatibleSuccessorCarrier
    (fallback : LocalSummaryAutomaton.{u, u, u} In₁ In₂)
    (hcarrier :
      PerStrategyWinningLiteralCombinedFreshPhaseLiveCompatibleSuccessorCarrierBookkeeping
        A) :
    StarFoldPackage A :=
  starFoldPackageOfExistsReadbackUpgrade A
    (exists_readbackUpgrade_of_phaseLiveCompatibleSuccessorCarrier A fallback
      hcarrier)

/-- Direct DPA synthesis decidability from the compatible carrier. -/
noncomputable def synthesisDecidable_direct_of_compatibleSuccessorCarrier
    (fallback : LocalSummaryAutomaton.{u, u, u} In₁ In₂)
    (hcarrier :
      PerStrategyWinningLiteralCombinedFreshPhaseLiveCompatibleSuccessorCarrierBookkeeping
        A) :
    Decidable
      (∃ strategy : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          A.Accepts (execution strategy env)) := by
  classical
  exact
    (starFoldPackageOfCompatibleSuccessorCarrier A fallback hcarrier
      ).synthesisDecidable_direct

end

end DetParityAutomaton

/-! ## Canonically compiled LTL objective -/

/-- Full finite-alphabet LTL synthesis from unconditional compatible-carrier
bookkeeping for every winning distributed strategy. -/
noncomputable def
    main_result_for_ltl_full_synthesis_finiteAlphabets_of_compatibleSuccessorCarrier
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
    (hcarrier :
      DetParityAutomaton.PerStrategyWinningLiteralCombinedFreshPhaseLiveCompatibleSuccessorCarrierBookkeeping
        ((PositiveLTL.canonicalLTLToDPACompiler interp dec).compile formula)) :
    Decidable
      (∃ strategy : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          LTL.Satisfies interp (execution strategy env) formula) :=
  main_result_for_ltl_full_synthesis_finiteAlphabets_of_existsReadbackUpgrade
    In₁ In₂ Out₁ Out₂ interp dec formula
      (DetParityAutomaton.exists_readbackUpgrade_of_phaseLiveCompatibleSuccessorCarrier
        ((PositiveLTL.canonicalLTLToDPACompiler interp dec).compile formula)
        fallback hcarrier)

end DistributedSynthesis
