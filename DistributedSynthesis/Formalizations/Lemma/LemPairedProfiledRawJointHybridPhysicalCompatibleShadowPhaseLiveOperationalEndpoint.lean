/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailHardRegimeAdapter
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveMain

/-!
# Final endpoint for operational root-aligned bookkeeping

This file removes the last quantifier plumbing between the concrete physical
controller construction and the existing unconditional readback and synthesis
backends.

For one fixed winning distributed strategy, the controller is chosen once,
outside the environment quantifier.  Each environment then owes exactly the
operational hard-regime bookkeeping:

* a root-aligned cut stream over the canonical recurrent operational-close
  clock;
* a root-aligned cut stream over the canonical strict-reversal
  operational-close clock; and
* the already installed fixed-output-tail bookkeeping.

The first two witnesses include their delayed tag, physical start, close-state
decoder, and exact decoder equality.  Everything after these three fields is
formal composition: operational cuts supply their own monotonicity and zero
law, cut streams supply physical acceptance, and the existing finite-controller
readback supplies the star fold and both synthesis endpoints.
-/

namespace DistributedSynthesis

universe u v x y s w

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

private abbrev PhysicalController :=
  FinitePairedPhysicalController.{u, v, x, y, w, w}
    In₁ In₂ Out₁ Out₂

/-- One physical controller whose operational bookkeeping is available for
every environment.  This is the exact fixed-strategy entrance to the final
acceptance backend. -/
theorem allEnvironmentPhysicalAcceptance_of_operationalHardRegimeBookkeeping
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (controller : PhysicalController (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂))
    (hoperational : ∀ env : EnvironmentSequence In₁ In₂,
      ProfiledRawJointHybridShadowPhaseLiveOperationalHardRegimeBookkeeping A
        strategy hwin controller env) :
    ∀ env : EnvironmentSequence In₁ In₂,
      Nonempty
        (A.FiniteGlobalMachinePhysicalAcceptance controller.globalMachine
          controller.globalOutputOne controller.globalOutputTwo env) := by
  intro env
  exact ⟨(hoperational env).physicalAcceptance A strategy hwin⟩

/-- One physical controller with operational bookkeeping has an accepting
actual trace in every environment. -/
theorem allEnvironmentAccepts_of_operationalHardRegimeBookkeeping
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (controller : PhysicalController (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂))
    (hoperational : ∀ env : EnvironmentSequence In₁ In₂,
      ProfiledRawJointHybridShadowPhaseLiveOperationalHardRegimeBookkeeping A
        strategy hwin controller env) :
    ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts
        (controller.globalMachine.globalMachineTraceWord
          controller.globalOutputOne controller.globalOutputTwo env) := by
  intro env
  exact A.finiteGlobalMachineTraceWord_accepts_of_physicalAcceptance
    controller.globalMachine controller.globalOutputOne
      controller.globalOutputTwo env
        ((hoperational env).physicalAcceptance A strategy hwin)

/-- Final strategy-indexed construction obligation for the operational route.
The finite controller may depend on the winning strategy, but not on the
environment. -/
def PerStrategyWinningShadowPhaseLiveOperationalHardRegimeBookkeeping : Prop :=
  ∀ (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)),
    ∃ controller :
        FinitePairedPhysicalController.{u, v, x, y, w, w}
          In₁ In₂ Out₁ Out₂,
      ∀ env : EnvironmentSequence In₁ In₂,
        ProfiledRawJointHybridShadowPhaseLiveOperationalHardRegimeBookkeeping A
          strategy hwin controller env

/-- Operational bookkeeping is exactly strong enough to fill the pre-existing
root-pinned controller endpoint. -/
theorem
    perStrategyWinningShadowPhaseLiveRootPinnedControllerBookkeeping_of_operational
    (hoperational :
      PerStrategyWinningShadowPhaseLiveOperationalHardRegimeBookkeeping.{u, v,
        x, y, s, w} A) :
    PerStrategyWinningShadowPhaseLiveRootPinnedControllerBookkeeping.{u, v, x,
      y, s, w} A := by
  intro strategy hwin
  obtain ⟨controller, hcontroller⟩ := hoperational strategy hwin
  refine ⟨controller, fun env ↦ ?_⟩
  exact (hcontroller env).controllerBookkeeping A strategy hwin

/-- The operational endpoint directly supplies the generic physical-acceptance
extraction premise. -/
theorem
    perStrategyWinningFinitePairedPhysicalControllerPhysicalAcceptance_of_operational
    (hoperational :
      PerStrategyWinningShadowPhaseLiveOperationalHardRegimeBookkeeping.{u, v,
        x, y, s, w} A) :
    PerStrategyWinningFinitePairedPhysicalControllerPhysicalAcceptance.{u, v,
      x, y, s, w} A := by
  intro strategy hwin
  obtain ⟨controller, hcontroller⟩ := hoperational strategy hwin
  exact ⟨controller,
    allEnvironmentPhysicalAcceptance_of_operationalHardRegimeBookkeeping A
      strategy hwin controller hcontroller⟩

/-- One-arrow readback extraction from the concrete operational endpoint. -/
theorem exists_readbackUpgrade_of_operationalHardRegimeBookkeeping
    (fallback : LocalSummaryAutomaton.{u, v, w} In₁ In₂)
    (hoperational :
      PerStrategyWinningShadowPhaseLiveOperationalHardRegimeBookkeeping.{u, v,
        x, y, s, w} A) :
    ∃ M : LocalSummaryAutomaton.{u, v, w} In₁ In₂,
      M.ReadbackUpgrade (Out₁ := Out₁) (Out₂ := Out₂) A := by
  exact
    exists_readbackUpgrade_of_finitePairedPhysicalControllerPhysicalAcceptance
      A fallback
        (perStrategyWinningFinitePairedPhysicalControllerPhysicalAcceptance_of_operational
          A hoperational)

end

end DetParityAutomaton

/-! ## Existing DPA and canonical-LTL synthesis conclusions -/

namespace DetParityAutomaton

universe q

variable {In₁ In₂ Out₁ Out₂ : Type q}
variable
  (A : DetParityAutomaton.{q, q}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-- Direct DPA synthesis decidability after the operational controller
construction. -/
noncomputable def synthesisDecidable_direct_of_operationalHardRegimeBookkeeping
    (fallback : LocalSummaryAutomaton.{q, q, q} In₁ In₂)
    (hoperational :
      PerStrategyWinningShadowPhaseLiveOperationalHardRegimeBookkeeping.{q, q,
        q, q, q, q} A) :
    Decidable
      (∃ strategy : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          A.Accepts (execution strategy env)) :=
  synthesisDecidable_direct_of_shadowPhaseLiveRootPinnedController A fallback
    (perStrategyWinningShadowPhaseLiveRootPinnedControllerBookkeeping_of_operational
      A hoperational)

end

end DetParityAutomaton

/-- Full finite-alphabet LTL synthesis from operational root-aligned
hard-regime bookkeeping for the canonical compiled DPA. -/
noncomputable def
    main_result_for_ltl_full_synthesis_finiteAlphabets_of_operationalHardRegimeBookkeeping
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
    (hoperational :
      DetParityAutomaton.PerStrategyWinningShadowPhaseLiveOperationalHardRegimeBookkeeping
        ((PositiveLTL.canonicalLTLToDPACompiler interp dec).compile formula)) :
    Decidable
      (∃ strategy : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          LTL.Satisfies interp (execution strategy env) formula) :=
  main_result_for_ltl_full_synthesis_finiteAlphabets_of_shadowPhaseLiveRootPinnedController
    In₁ In₂ Out₁ Out₂ interp dec formula fallback
      (DetParityAutomaton.perStrategyWinningShadowPhaseLiveRootPinnedControllerBookkeeping_of_operational
        ((PositiveLTL.canonicalLTLToDPACompiler interp dec).compile formula)
        hoperational)

end DistributedSynthesis
