/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossControllerTraceInvariant

/-!
# Readback socket for a repaired phase/live-stage controller

This file fixes the exact downstream finish line for the local carrier repair.
The repaired endpoint maps need not be compared with the obsolete
pending-only controller.  They only have to construct one finite paired
physical controller and, for every environment, fill the already established
`FinitePairedPhysicalControllerLiteralCrossTraceExtraction` interface.

Concretely that interface asks for:

* one graph-split reachable-state invariant, with initial, strict-left,
  strict-right, simultaneous, and Moore-output equations;
* eventual strict-right and strict-left tail parity;
* in each of the two hard regimes, one canonical literal-close schedule with
  the DPA entry state and emitted physical records aligned at its cuts.

Everything after those local and operational facts is already automatic:
trace equality, canonical epoch slices, the four-regime acceptance split,
the direct local presentation, reachable-belief uniformity, and finally
`ReadbackUpgrade`.

The preferred construction route for the graph-split invariant is smaller
still.  A repaired fibre of a `FiniteExactClosingBlindFamily` need only prove
`ExactClosingSelectedTraceLaws`: one initial selected pair and the three graph
cases (`strictRight`, `strictLeft`, and `both`), each returning the next
selected pair and the two exact physical-output equations.  The existing
adapters `bankSelectedTraceLaws_of_fibre`,
`bankMealyTraceInvariant_of_fibre`, and
`LiteralCrossMealyTraceInvariant.toMooreTraceInvariant` then add the dependent
bank, acknowledgement relay, arbitrary blind-depth invariant, and Moore timing
without further model-specific transition proofs.

No executable transition in this adapter receives a graph, orientation,
hierarchy side, leader bit, strict-leader bit, history, or semantic view.
-/

namespace DistributedSynthesis

universe u v x y s w

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

/-- Direct constructor-shaped endpoint for the repaired carrier.

`controllerOf` is the one finite local controller selected for a winning
strategy.  `hextract` contains only its per-environment operational trace
facts.  The theorem packages those data into the repository's existing
strategy-indexed extraction and invokes the checked readback chain. -/
theorem exists_readbackUpgrade_of_phaseLiveStageController
    (fallback : LocalSummaryAutomaton.{u, v, w} In₁ In₂)
    (controllerOf :
      ∀ (strategy : StrategyPair In₁ In₂ Out₁ Out₂),
        (∀ env : EnvironmentSequence In₁ In₂,
          A.Accepts (execution strategy env)) →
            FinitePairedPhysicalController.{u, v, x, y, w, w}
              In₁ In₂ Out₁ Out₂)
    (hextract :
      ∀ (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
        (hwin : ∀ env : EnvironmentSequence In₁ In₂,
          A.Accepts (execution strategy env))
        (env : EnvironmentSequence In₁ In₂),
        Nonempty
          (FinitePairedPhysicalControllerLiteralCrossTraceExtraction A
            strategy (controllerOf strategy hwin) env)) :
    ∃ M : LocalSummaryAutomaton.{u, v, w} In₁ In₂,
      M.ReadbackUpgrade (Out₁ := Out₁) (Out₂ := Out₂) A := by
  apply exists_readbackUpgrade_of_finitePairedPhysicalControllerTraceExtraction
    A fallback
  intro strategy hwin
  exact ⟨controllerOf strategy hwin, hextract strategy hwin⟩

end

end DetParityAutomaton

end DistributedSynthesis
