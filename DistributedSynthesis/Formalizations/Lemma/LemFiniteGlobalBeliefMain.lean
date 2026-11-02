/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteGlobalBeliefReadback
import DistributedSynthesis.Formalizations.Theorem.ThmMainSummaryWinner

/-!
# Full-LTL endpoint from strategy-indexed finite global belief machines

This file is only the final generic composition.  The mathematical premise is
`PerStrategyWinningFiniteGlobalBeliefMachine` for the canonically compiled
objective.  The belief readback turns it into an existential
`ReadbackUpgrade`; the existing full-synthesis endpoint then supplies the
finite-alphabet main decision procedure.

No model-specific round, epoch, leader, orientation, or hidden-bit datum is
introduced here.
-/

namespace DistributedSynthesis

/-- The full finite-alphabet `{←,→,↔}` LTL synthesis endpoint from the exact
strategy-indexed finite-global-machine premise consumed by the generic belief
readback.

All downstream construction is already unconditional: the canonical LTL-to-DPA
compiler, the administrative trivial tree target, the summary epoch
compilation, and finite-game search.  Thus `hextract` is the sole mathematical
construction premise beyond the ordinary finite-alphabet and decidability
typeclasses displayed in the statement. -/
noncomputable def
    main_result_for_ltl_full_synthesis_finiteAlphabets_of_finiteGlobalBeliefMachine
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
    (hextract :
      DetParityAutomaton.PerStrategyWinningFiniteGlobalBeliefMachine
        ((PositiveLTL.canonicalLTLToDPACompiler interp dec).compile formula)
        fallback) :
    Decidable
      (∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          LTL.Satisfies interp (execution σ env) formula) :=
  main_result_for_ltl_full_synthesis_finiteAlphabets_of_existsReadbackUpgrade
    In₁ In₂ Out₁ Out₂ interp dec formula
    (DetParityAutomaton.exists_readbackUpgrade_of_finiteGlobalBeliefMachine
      ((PositiveLTL.canonicalLTLToDPACompiler interp dec).compile formula)
      fallback hextract)

end DistributedSynthesis
