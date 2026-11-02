/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralPhaseLivePriorityReadback
import DistributedSynthesis.Formalizations.Theorem.ThmMainSummaryWinner

/-!
# Full-LTL endpoint of the phase-live priority construction

This file performs only the already verified final composition.  Applied to
the canonical DPA for a full LTL formula, the phase-live priority construction
produces `ReadbackUpgrade`, and the existing main-theorem backend decides
distributed realizability in the full `{left,right,both}` model.

Consequently the sole mathematical target remaining on this route is the
universal phase-live priority property itself.  No additional star, fringe,
journal, hierarchy-observer, or literature premise occurs below.
-/

namespace DistributedSynthesis

/-- Full finite-alphabet LTL synthesis from the concrete phase-live priority
theorem for the canonically compiled objective. -/
noncomputable def
    main_result_for_ltl_full_synthesis_finiteAlphabets_of_phaseLivePriorityAcceptance
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
    (hphase :
      DetParityAutomaton.PerStrategyWinningLiteralCombinedFreshPhaseLivePriorityAcceptance
        ((PositiveLTL.canonicalLTLToDPACompiler interp dec).compile formula)) :
    Decidable
      (∃ strategy : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          LTL.Satisfies interp (execution strategy env) formula) :=
  main_result_for_ltl_full_synthesis_finiteAlphabets_of_existsReadbackUpgrade
    In₁ In₂ Out₁ Out₂ interp dec formula
      (DetParityAutomaton.exists_readbackUpgrade_of_phaseLivePriorityAcceptance
        ((PositiveLTL.canonicalLTLToDPACompiler interp dec).compile formula)
        fallback hphase)

/-- Full finite-alphabet LTL synthesis from the anchor-free physical
acceptance package produced by the carried whole-block route. -/
noncomputable def
    main_result_for_ltl_full_synthesis_finiteAlphabets_of_phaseLivePhysicalAcceptance
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
    (hphase :
      DetParityAutomaton.PerStrategyWinningLiteralCombinedFreshPhaseLivePhysicalAcceptance
        ((PositiveLTL.canonicalLTLToDPACompiler interp dec).compile formula)) :
    Decidable
      (∃ strategy : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          LTL.Satisfies interp (execution strategy env) formula) :=
  main_result_for_ltl_full_synthesis_finiteAlphabets_of_existsReadbackUpgrade
    In₁ In₂ Out₁ Out₂ interp dec formula
      (DetParityAutomaton.exists_readbackUpgrade_of_phaseLivePhysicalAcceptance
        ((PositiveLTL.canonicalLTLToDPACompiler interp dec).compile formula)
        fallback hphase)

end DistributedSynthesis
