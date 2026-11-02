/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshPhaseActivatedRecurrentReroot
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshPendingOnlyAcceptanceIntegration
import DistributedSynthesis.Formalizations.Lemma.LemFinitePairedPhysicalControllerReadback

/-!
# Direct readback for the phase-activated controller

The phase-activated acknowledged controller is a genuine finite local
controller.  This file records the shortest possible consumer for the
positive activation route: once its physical word is accepting for every
environment, the generic finite-controller theorem supplies
`ReadbackUpgrade` immediately.

This endpoint is deliberately independent of the phase-live compatible-table
bookkeeping.  In particular, it does not ask the phase-live and activated
controllers to agree after activation, and it introduces no hierarchy-side,
leader, graph-regime, or semantic-view input at either endpoint.
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

private abbrev DefaultPackage
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)) :=
  literalCombinedFreshPendingOnlyDefaultPackage A strategy hwin

private abbrev ActivatedController
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)) :=
  (DefaultPackage A strategy hwin
    ).literalCombinedFreshPhaseActivatedPhysicalController A strategy hwin

/-! ## Exact alternative finish line -/

/-- Every winning strategy admits the fixed phase-activated finite local
controller whose direct physical word is accepting for every environment.

The controller is selected before the environment is quantified.  Only the
proof of acceptance may inspect the proof-side graph regime. -/
def PerStrategyWinningLiteralCombinedFreshPhaseActivatedAcceptance : Prop :=
  ∀ (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)),
    ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts
        ((ActivatedController A strategy hwin).globalMachine.globalMachineTraceWord
            (ActivatedController A strategy hwin).globalOutputOne
            (ActivatedController A strategy hwin).globalOutputTwo env)

/-- The activated endpoint is already the generic finite paired-controller
endpoint consumed by local-summary readback. -/
theorem
    perStrategyWinningFinitePairedPhysicalController_of_phaseActivated
    (hactivated :
      PerStrategyWinningLiteralCombinedFreshPhaseActivatedAcceptance A) :
    PerStrategyWinningFinitePairedPhysicalController.{u, v, x, y, s,
      max (max (max (max s u) v) x) y} A := by
  intro strategy hwin
  refine ⟨ActivatedController A strategy hwin, ?_⟩
  exact hactivated strategy hwin

/-- One-arrow extraction of the finite local-summary retraction from physical
acceptance of the activated controller. -/
theorem exists_readbackUpgrade_of_phaseActivatedAcceptance
    (fallback : LocalSummaryAutomaton.{u, v,
      max (max (max (max s u) v) x) y} In₁ In₂)
    (hactivated :
      PerStrategyWinningLiteralCombinedFreshPhaseActivatedAcceptance A) :
    ∃ M : LocalSummaryAutomaton.{u, v,
        max (max (max (max s u) v) x) y} In₁ In₂,
      M.ReadbackUpgrade (Out₁ := Out₁) (Out₂ := Out₂) A := by
  exact exists_readbackUpgrade_of_finitePairedPhysicalController A fallback
    (perStrategyWinningFinitePairedPhysicalController_of_phaseActivated A
      hactivated)

end

end DetParityAutomaton

end DistributedSynthesis
