/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveMixedHardRegimeAdapter
import DistributedSynthesis.Formalizations.Lemma.LemStarSummaryHosting
import DistributedSynthesis.Formalizations.Theorem.ThmMainSummaryWinner

/-!
# Closed hard-regime acceptance endpoint

This module records the shortest stable handoff from the physical controller
construction to the unconditional synthesis backends.  In particular, once a
closed persistent-tail certificate proves acceptance of the *actual* physical
controller word, no root-aligned cut stream and no further trace equality is
needed downstream.

For one environment the interface keeps exactly three independent facts:

* direct acceptance in the recurrent-`.both` regime;
* direct acceptance in the persistent strict-reversal regime; and
* the existing bookkeeping for the two eventually fixed strict tails.

The graph-regime split is proof-side.  No graph, orientation, hierarchy side,
leader bit, tag, or certificate is passed to either executable process.
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

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

private abbrev PhysicalController :=
  FinitePairedPhysicalController.{u, v, x, y, w, w}
    In₁ In₂ Out₁ Out₂

/-- The minimal environment-local acceptance boundary after the recurrent and
persistent-tail constructions have been closed.  The two productive regimes
state acceptance of the controller's actual trace, while the eventually
constant regimes retain their specialized output-tail proof. -/
structure ProfiledRawJointHybridClosedHardRegimeAcceptanceBookkeeping
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
  fixed : EventuallyInstalledOutputTailBookkeeping A controller env

namespace ProfiledRawJointHybridClosedHardRegimeAcceptanceBookkeeping

/-- Direct acceptance in each productive regime and the established fixed-tail
bookkeeping fill the repository's exhaustive four-regime physical package. -/
noncomputable def physicalAcceptance
    {controller : PhysicalController (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {env : EnvironmentSequence In₁ In₂}
    (bookkeeping :
      ProfiledRawJointHybridClosedHardRegimeAcceptanceBookkeeping A controller
        env) :
    A.FiniteGlobalMachinePhysicalAcceptance controller.globalMachine
      controller.globalOutputOne controller.globalOutputTwo env := by
  let fixed := bookkeeping.fixed.toEventuallyInstalledFixedTailBookkeeping A
  exact {
    recurrent := fun hboth ↦
      (A.finiteGlobalMachinePhysicalAcceptance_of_accepts
        controller.globalMachine controller.globalOutputOne
          controller.globalOutputTwo env (bookkeeping.recurrent hboth)
        ).recurrent hboth
    alternatingTail := fun hreversal ↦
      (A.finiteGlobalMachinePhysicalAcceptance_of_accepts
        controller.globalMachine controller.globalOutputOne
          controller.globalOutputTwo env (bookkeeping.reversal hreversal)
        ).alternatingTail hreversal
    strictRightTail := fixed.rightTailParity A
    strictLeftTail := fixed.leftTailParity A }

/-- The older mixed boundary implies the direct closed-acceptance boundary.
This is useful when a caller already constructed the tagged reversal stream. -/
noncomputable def ofMixedHardRegimeBookkeeping
    {controller : PhysicalController (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {env : EnvironmentSequence In₁ In₂}
    (bookkeeping :
      ProfiledRawJointHybridShadowPhaseLiveMixedHardRegimeBookkeeping A
        strategy hwin controller env) :
    ProfiledRawJointHybridClosedHardRegimeAcceptanceBookkeeping A controller
      env where
  recurrent := bookkeeping.recurrent
  reversal hreversal := by
    let witness := Classical.choice (bookkeeping.reversal hreversal)
    let bundle := witness.publicHardCertificateBundle A strategy hwin
    exact bundle.2.2.2.accepts A strategy hwin
  fixed := bookkeeping.fixed

end ProfiledRawJointHybridClosedHardRegimeAcceptanceBookkeeping

/-! ## Strategy-indexed extraction -/

/-- The precise construction premise remaining upstream: for a fixed winning
strategy, choose one finite local controller before the environment, then
close its recurrent, persistent-reversal, and fixed-tail acceptance branches
for every environment. -/
def PerStrategyWinningProfiledRawJointHybridClosedHardRegimeAcceptance : Prop :=
  ∀ (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)),
    ∃ controller :
        FinitePairedPhysicalController.{u, v, x, y, w, w}
          In₁ In₂ Out₁ Out₂,
      ∀ env : EnvironmentSequence In₁ In₂,
        ProfiledRawJointHybridClosedHardRegimeAcceptanceBookkeeping A controller
          env

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Closed regime acceptance is exactly sufficient for the generic finite
physical-controller acceptance interface. -/
theorem
    perStrategyWinningFinitePairedPhysicalControllerPhysicalAcceptance_of_closedHardRegimes
    (hclosed :
      PerStrategyWinningProfiledRawJointHybridClosedHardRegimeAcceptance.{u,
        v, x, y, s, w} A) :
    PerStrategyWinningFinitePairedPhysicalControllerPhysicalAcceptance.{u, v,
      x, y, s, w} A := by
  intro strategy hwin
  obtain ⟨controller, hcontroller⟩ := hclosed strategy hwin
  refine ⟨controller, fun env ↦ ⟨?_⟩⟩
  exact (hcontroller env).physicalAcceptance A

omit [Inhabited In₁] [Inhabited In₂] in
/-- One-arrow extraction of the finite local-summary readback. -/
theorem exists_readbackUpgrade_of_closedHardRegimeAcceptance
    (fallback : LocalSummaryAutomaton.{u, v, w} In₁ In₂)
    (hclosed :
      PerStrategyWinningProfiledRawJointHybridClosedHardRegimeAcceptance.{u,
        v, x, y, s, w} A) :
    ∃ M : LocalSummaryAutomaton.{u, v, w} In₁ In₂,
      M.ReadbackUpgrade (Out₁ := Out₁) (Out₂ := Out₂) A := by
  exact
    exists_readbackUpgrade_of_finitePairedPhysicalControllerPhysicalAcceptance
      A fallback
        (perStrategyWinningFinitePairedPhysicalControllerPhysicalAcceptance_of_closedHardRegimes
          A hclosed)

end

end DetParityAutomaton

/-! ## Star, DPA, and finite-alphabet LTL endpoints -/

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
variable [DecidableEq A.State]

/-- A closed hard-regime construction supplies the complete star fold through
the already proved local-summary hosting theorem. -/
noncomputable def starFoldPackageOfClosedHardRegimeAcceptance
    (fallback : LocalSummaryAutomaton.{q, q, q} In₁ In₂)
    (hclosed :
      PerStrategyWinningProfiledRawJointHybridClosedHardRegimeAcceptance.{q,
        q, q, q, q, q} A) :
    StarFoldPackage A :=
  starFoldPackageOfExistsReadbackUpgrade A
    (exists_readbackUpgrade_of_closedHardRegimeAcceptance A fallback hclosed)

/-- Direct DPA synthesis decidability, using the constant-observation star
game after the closed hard-regime handoff. -/
noncomputable def synthesisDecidable_direct_of_closedHardRegimeAcceptance
    (fallback : LocalSummaryAutomaton.{q, q, q} In₁ In₂)
    (hclosed :
      PerStrategyWinningProfiledRawJointHybridClosedHardRegimeAcceptance.{q,
        q, q, q, q, q} A) :
    Decidable
      (∃ strategy : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          A.Accepts (execution strategy env)) :=
  (starFoldPackageOfClosedHardRegimeAcceptance A fallback hclosed
    ).synthesisDecidable_direct

end


end DetParityAutomaton

/-- Full finite-alphabet LTL synthesis once the canonical compiled DPA has a
closed hard-regime finite-controller construction. -/
noncomputable def
    main_result_for_ltl_full_synthesis_finiteAlphabets_of_closedHardRegimeAcceptance
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
    (hclosed :
      DetParityAutomaton.PerStrategyWinningProfiledRawJointHybridClosedHardRegimeAcceptance
        ((PositiveLTL.canonicalLTLToDPACompiler interp dec).compile formula)) :
    Decidable
      (∃ strategy : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          LTL.Satisfies interp (execution strategy env) formula) :=
  main_result_for_ltl_full_synthesis_finiteAlphabets_of_existsReadbackUpgrade
    In₁ In₂ Out₁ Out₂ interp dec formula
      (DetParityAutomaton.exists_readbackUpgrade_of_closedHardRegimeAcceptance
        ((PositiveLTL.canonicalLTLToDPACompiler interp dec).compile formula)
        fallback hclosed)

end DistributedSynthesis
