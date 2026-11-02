/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridClosedHardRegimeEndpoint

/-!
# Direct closed-regime endpoint for one physical controller

Some concrete local controllers use linked payload tables rather than the
older sibling-move carrier expected by `EventuallyInstalledOutputTailBookkeeping`.
For those controllers the honest fixed-tail result is acceptance of the
controller's actual word (obtained from an accepted linked word and an exact
output-tail equality).  This module records the corresponding minimal
four-regime endpoint.

All four graph regimes are proof-side selectors.  No graph side, hierarchy,
leader bit, tag, or acceptance witness is supplied to either local machine.
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

/-- Acceptance of the actual physical word in each exhaustive graph regime.
This is deliberately controller-agnostic and therefore also applies to the
linked-payload FullRestart carrier. -/
structure ProfiledRawJointHybridClosedDirectRegimeAcceptanceBookkeeping
    (controller : PhysicalController (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂))
    (env : EnvironmentSequence In₁ In₂) : Prop where
  recurrent :
    GraphBothRecurrent (fun n ↦ (env n).graph) →
      A.Accepts
        (controller.globalMachine.globalMachineTraceWord
          controller.globalOutputOne controller.globalOutputTwo env)
  reversal :
    PersistentStrictReversalTail (fun n ↦ (env n).graph) →
      A.Accepts
        (controller.globalMachine.globalMachineTraceWord
          controller.globalOutputOne controller.globalOutputTwo env)
  strictRight :
    EventuallyStrictRight (fun n ↦ (env n).graph) →
      A.Accepts
        (controller.globalMachine.globalMachineTraceWord
          controller.globalOutputOne controller.globalOutputTwo env)
  strictLeft :
    EventuallyStrictLeft (fun n ↦ (env n).graph) →
      A.Accepts
        (controller.globalMachine.globalMachineTraceWord
          controller.globalOutputOne controller.globalOutputTwo env)

namespace ProfiledRawJointHybridClosedDirectRegimeAcceptanceBookkeeping

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- The four graph regimes are exhaustive, so direct regime acceptance is
already direct acceptance of the controller word. -/
theorem accepts
    {controller : PhysicalController (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {env : EnvironmentSequence In₁ In₂}
    (bookkeeping :
      ProfiledRawJointHybridClosedDirectRegimeAcceptanceBookkeeping A
        controller env) :
    A.Accepts
      (controller.globalMachine.globalMachineTraceWord
        controller.globalOutputOne controller.globalOutputTwo env) := by
  rcases environment_physical_acceptance_regime env with
    hboth | hreversal | hright | hleft
  · exact bookkeeping.recurrent hboth
  · exact bookkeeping.reversal hreversal
  · exact bookkeeping.strictRight hright
  · exact bookkeeping.strictLeft hleft

/-- Compatibility adapter for callers that still consume the physical
four-regime package. -/
noncomputable def physicalAcceptance
    {controller : PhysicalController (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {env : EnvironmentSequence In₁ In₂}
    (bookkeeping :
      ProfiledRawJointHybridClosedDirectRegimeAcceptanceBookkeeping A
        controller env) :
    A.FiniteGlobalMachinePhysicalAcceptance controller.globalMachine
      controller.globalOutputOne controller.globalOutputTwo env :=
  A.finiteGlobalMachinePhysicalAcceptance_of_accepts controller.globalMachine
    controller.globalOutputOne controller.globalOutputTwo env
      (bookkeeping.accepts A)

end ProfiledRawJointHybridClosedDirectRegimeAcceptanceBookkeeping

/-- Strategy-indexed construction boundary for direct acceptance in all four
proof-side graph regimes. -/
def PerStrategyWinningProfiledRawJointHybridClosedDirectRegimeAcceptance :
    Prop :=
  ∀ (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)),
    ∃ controller :
        FinitePairedPhysicalController.{u, v, x, y, w, w}
          In₁ In₂ Out₁ Out₂,
      ∀ env : EnvironmentSequence In₁ In₂,
        ProfiledRawJointHybridClosedDirectRegimeAcceptanceBookkeeping A
          controller env

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Direct closed-regime bookkeeping supplies the repository's standard
all-environment finite-controller endpoint. -/
theorem
    perStrategyWinningFinitePairedPhysicalController_of_closedDirectRegimes
    (hclosed :
      PerStrategyWinningProfiledRawJointHybridClosedDirectRegimeAcceptance.{u,
        v, x, y, s, w} A) :
    PerStrategyWinningFinitePairedPhysicalController.{u, v, x, y, s, w} A := by
  intro strategy hwin
  obtain ⟨controller, hcontroller⟩ := hclosed strategy hwin
  exact ⟨controller, fun env ↦ (hcontroller env).accepts A⟩

omit [Inhabited In₁] [Inhabited In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁]
    [DecidableEq In₂] in
/-- One-arrow extraction of the local-summary readback. -/
theorem exists_readbackUpgrade_of_closedDirectRegimeAcceptance
    (fallback : LocalSummaryAutomaton.{u, v, w} In₁ In₂)
    (hclosed :
      PerStrategyWinningProfiledRawJointHybridClosedDirectRegimeAcceptance.{u,
        v, x, y, s, w} A) :
    ∃ M : LocalSummaryAutomaton.{u, v, w} In₁ In₂,
      M.ReadbackUpgrade (Out₁ := Out₁) (Out₂ := Out₂) A := by
  exact exists_readbackUpgrade_of_finitePairedPhysicalController A fallback
    (perStrategyWinningFinitePairedPhysicalController_of_closedDirectRegimes
      A hclosed)

end

end DetParityAutomaton

end DistributedSynthesis
