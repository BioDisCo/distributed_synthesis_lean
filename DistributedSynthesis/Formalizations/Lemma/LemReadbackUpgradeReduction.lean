/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmSummaryEpochCertificate
import DistributedSynthesis.Formalizations.Theorem.ThmSummaryMeasurableTransfer

/-!
# Readback from a summary-observable winner

`LocalSummaryAutomaton.ReadbackUpgrade M A` requires that every realizable
objective admit a winning strategy given by output tables over `M`.
The constructions below derive this property from the existence of a
summary-observable winning controller in the finite epoch game.

The implication uses `summaryEpochTransformer_strategySound` and
`SummaryTracking.strategySound`. The existence of the summary-observable
winner is an explicit hypothesis; this module proves the readback step.
-/

namespace DistributedSynthesis

universe u v w a s z o b x

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type w} {Out₂ : Type a}

namespace DetParityAutomaton

open FiniteEpochTransformer

variable
  [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
  [Inhabited Out₁] [Inhabited Out₂]
  (A :
    DetParityAutomaton.{max u v w a, max u v w a}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))
  (M : LocalSummaryAutomaton.{u, v, max u v w a} In₁ In₂)

/-- **The finite-summary winner obligation for the θ̄-game.**  Whenever the objective is realizable by a
distributed strategy, the θ̄-transformer's finite game admits a *summary-observable* winning
controller -- one whose moves factor through the current summaries
(`SummaryTracking.summaryController`).  A checked derivation from the published finite-state theorem
still requires the model-specific finite-game/hierarchy adapter; therefore this proposition must not
be described as a classical theorem on its own.  It replaces the older boundary-game formulation but
has the same remaining completeness content. -/
def SummaryObservableWinnerCertificate : Prop :=
  ∀ σ : StrategyPair In₁ In₂ Out₁ Out₂,
    (∀ env : EnvironmentSequence In₁ In₂, A.Accepts (execution σ env)) ->
      ∃ (outputOne : M.Summary Proc.one -> Out₁) (outputTwo : M.Summary Proc.two -> Out₂),
        ∀ environment :
            EnvironmentCode (A.summaryEpochTransformer (Out₁ := Out₁) (Out₂ := Out₂) M),
          roundAwareGameWins (A.summaryEpochTransformer M) (A.summaryInitialBoundary M)
            ((A.summaryEpochTransformerTracking M).summaryController outputOne outputTwo)
            environment

omit [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [Inhabited Out₁]
    [Inhabited Out₂] in
/-- **`ReadbackUpgrade` reduces to the summary-observable winner certificate**, via the built
extraction (`summaryEpochTransformer_strategySound`).  The summary controller factors through the
summaries by construction (`hfactor` is `rfl`), so its finite-game win reads back to an
all-environment-accepted distributed strategy.  This machine-checks the extraction half of paper
`prop:starcomplete`; the finite-game winner is the external Berwanger import. -/
theorem readbackUpgrade_of_summaryObservableWinner
    (hcert : SummaryObservableWinnerCertificate A M) :
    M.ReadbackUpgrade (Out₁ := Out₁) (Out₂ := Out₂) A := by
  intro σ hσ
  obtain ⟨outputOne, outputTwo, hwins⟩ := hcert σ hσ
  exact
    ⟨outputOne, outputTwo,
      A.summaryEpochTransformer_strategySound M outputOne outputTwo
        ((A.summaryEpochTransformerTracking M).summaryController outputOne outputTwo)
        (fun _ _ => rfl) hwins⟩

end DetParityAutomaton

end DistributedSynthesis
