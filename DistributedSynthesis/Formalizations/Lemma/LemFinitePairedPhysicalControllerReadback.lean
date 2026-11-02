/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenWitnessedPhysicalRoundAdapter
import DistributedSynthesis.Formalizations.Lemma.LemFiniteGlobalBeliefReadback
import DistributedSynthesis.Formalizations.Lemma.LemFiniteGlobalBeliefPhysicalAcceptanceSplit

/-!
# Direct readback for a finite paired physical controller

`FinitePairedPhysicalController` already is the finite local object required by
the model.  This file packages its product of local controls as a finite global
round machine and applies the generic belief readback.  It removes the need to
invent dummy epoch/query coordinates merely to reach `ReadbackUpgrade`.

The global product below is proof-side.  Its transition is definitionally the
product of the four endpoint-local maps.  In particular none of the executable
maps receives a graph, orientation, leader bit, strict-leader bit, or history.
-/

namespace DistributedSynthesis

universe u v x y c₁ c₂ s w

namespace FinitePairedPhysicalController

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (controller : FinitePairedPhysicalController.{u, v, x, y, c₁, c₂}
    In₁ In₂ Out₁ Out₂)

/-! ## The direct finite global product -/

/-- Proof-side product of the two genuine finite local controls. -/
noncomputable def globalMachine :
    FiniteGlobalRoundMachine.{u, v, max c₁ c₂} In₁ In₂ where
  State := controller.OneControl × controller.TwoControl
  stateFinite := inferInstance
  initial := (controller.initialOne, controller.initialTwo)
  step := controller.advanceControls

/-- Process one's Moore output reads only its own component. -/
def globalOutputOne : controller.globalMachine.State → Out₁ :=
  fun state ↦ controller.outputOne state.1

/-- Process-two mirror. -/
def globalOutputTwo : controller.globalMachine.State → Out₂ :=
  fun state ↦ controller.outputTwo state.2

@[simp] theorem globalMachine_initial :
    controller.globalMachine.initial =
      (controller.initialOne, controller.initialTwo) :=
  rfl

@[simp] theorem globalMachine_step
    (state : controller.globalMachine.State)
    (round : EnvironmentRound In₁ In₂) :
    controller.globalMachine.step state round =
      controller.advanceControls state round :=
  rfl

/-! ## Local presentation and automatic belief uniformity -/

/-- The direct product is presented by the controller's original endpoint
maps, definitionally. -/
noncomputable def localPresentation [Fintype In₁] [Fintype In₂] :
    controller.globalMachine.LocalPresentation controller.globalOutputOne
      controller.globalOutputTwo where
  ControlOne := controller.OneControl
  ControlTwo := controller.TwoControl
  initialOne := controller.initialOne
  initialTwo := controller.initialTwo
  localOutputOne := controller.outputOne
  localOutputTwo := controller.outputTwo
  noRecvOne := controller.noRecvOne
  noRecvTwo := controller.noRecvTwo
  recv := fun one two inputOne inputTwo ↦
    (controller.recvOne one inputOne two inputTwo,
      controller.recvTwo two inputTwo one inputOne)
  RepOne := fun control state ↦ control = state.1
  RepTwo := fun control state ↦ control = state.2
  initialRepOne := rfl
  initialRepTwo := rfl
  outputOne_eq := by
    intro control state hrep
    simpa [globalOutputOne] using congrArg controller.outputOne hrep.symm
  outputTwo_eq := by
    intro control state hrep
    simpa [globalOutputTwo] using congrArg controller.outputTwo hrep.symm
  noRecvOne_rep := by
    intro control state hrep inputOne hidden
    subst control
    rfl
  noRecvTwo_rep := by
    intro control state hrep inputTwo hidden
    subst control
    rfl
  recvOne_rep := by
    intro one two state hone htwo inputOne inputTwo graph hgraph
    subst one
    subst two
    rcases hgraph with rfl | rfl <;> rfl
  recvTwo_rep := by
    intro one two state hone htwo inputOne inputTwo graph hgraph
    subst one
    subst two
    rcases hgraph with rfl | rfl <;> rfl

/-- Reachable-belief output uniformity is a consequence of genuine locality,
not an additional extraction premise. -/
theorem reachableBeliefsUniform [Fintype In₁] [Fintype In₂] :
    controller.globalMachine.ReachableBeliefsUniform
      controller.globalOutputOne controller.globalOutputTwo :=
  FiniteGlobalRoundMachine.LocalPresentation.reachableBeliefsUniform
    controller.globalMachine controller.globalOutputOne
      controller.globalOutputTwo controller.localPresentation

end FinitePairedPhysicalController

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable [Fintype In₁] [Fintype In₂]
variable [Inhabited Out₁] [Inhabited Out₂]
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

/-! ## Strategy-indexed extraction endpoint -/

/-- For each winning strategy, construct a genuinely local finite controller
whose direct physical trace is accepting.  The control types may depend on the
strategy but stay in the fixed universe `w`. -/
def PerStrategyWinningFinitePairedPhysicalController : Prop :=
  ∀ strategy : StrategyPair In₁ In₂ Out₁ Out₂,
    (∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)) →
      ∃ controller :
          FinitePairedPhysicalController.{u, v, x, y, w, w}
            In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          A.Accepts
            (controller.globalMachine.globalMachineTraceWord
              controller.globalOutputOne controller.globalOutputTwo env)

/-- A convenient stronger endpoint when the constructed local controller is
proved pointwise equal to the supplied winning strategy. -/
def PerStrategyWinningFinitePairedPhysicalControllerAgreement : Prop :=
  ∀ strategy : StrategyPair In₁ In₂ Out₁ Out₂,
    (∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)) →
      ∃ controller :
          FinitePairedPhysicalController.{u, v, x, y, w, w}
            In₁ In₂ Out₁ Out₂,
        controller.globalMachine.StrategyOutputAgreement
          controller.globalOutputOne controller.globalOutputTwo strategy

/-- Acceptance-facing form used by epoch proofs: the genuinely local
controller is fixed once, and each environment supplies the existing
four-regime physical-acceptance package for its direct trace. -/
def PerStrategyWinningFinitePairedPhysicalControllerPhysicalAcceptance : Prop :=
  ∀ strategy : StrategyPair In₁ In₂ Out₁ Out₂,
    (∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)) →
      ∃ controller :
          FinitePairedPhysicalController.{u, v, x, y, w, w}
            In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          Nonempty
            (A.FiniteGlobalMachinePhysicalAcceptance controller.globalMachine
              controller.globalOutputOne controller.globalOutputTwo env)

omit [Fintype In₁] [Fintype In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Pointwise strategy agreement supplies direct trace acceptance. -/
theorem perStrategyWinningFinitePairedPhysicalController_of_agreement
    (hextract :
      PerStrategyWinningFinitePairedPhysicalControllerAgreement.{u, v, x, y,
        s, w} A) :
    PerStrategyWinningFinitePairedPhysicalController.{u, v, x, y, s, w} A := by
  intro strategy hwin
  obtain ⟨controller, hagrees⟩ := hextract strategy hwin
  refine ⟨controller, ?_⟩
  exact controller.globalMachine.globalMachine_allEnvironment_of_strategyOutputAgreement
    controller.globalOutputOne controller.globalOutputTwo strategy hagrees
      A.Accepts hwin

omit [Fintype In₁] [Fintype In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- The generic four-regime theorem consumes the physical packages, leaving
only direct all-environment acceptance of the same local controller. -/
theorem
    perStrategyWinningFinitePairedPhysicalController_of_physicalAcceptance
    (hextract :
      PerStrategyWinningFinitePairedPhysicalControllerPhysicalAcceptance.{u,
        v, x, y, s, w} A) :
    PerStrategyWinningFinitePairedPhysicalController.{u, v, x, y, s, w} A := by
  intro strategy hwin
  obtain ⟨controller, hphysical⟩ := hextract strategy hwin
  refine ⟨controller, fun env ↦ ?_⟩
  obtain ⟨physical⟩ := hphysical env
  exact A.finiteGlobalMachineTraceWord_accepts_of_physicalAcceptance
    controller.globalMachine controller.globalOutputOne
      controller.globalOutputTwo env physical

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Direct finite local controllers instantiate the generic finite-global
belief-machine route without an auxiliary epoch adapter. -/
theorem perStrategyWinningFiniteGlobalBeliefMachine_of_pairedPhysicalController
    (fallback : LocalSummaryAutomaton.{u, v, w} In₁ In₂)
    (hextract :
      PerStrategyWinningFinitePairedPhysicalController.{u, v, x, y, s, w}
        A) :
    PerStrategyWinningFiniteGlobalBeliefMachine A fallback := by
  intro strategy hwin
  obtain ⟨controller, haccepts⟩ := hextract strategy hwin
  exact ⟨controller.globalMachine, controller.globalOutputOne,
    controller.globalOutputTwo, controller.reachableBeliefsUniform, haccepts⟩

/-- Final one-arrow consumer for the literal/product carrier now under
construction. -/
theorem exists_readbackUpgrade_of_finitePairedPhysicalController
    (fallback : LocalSummaryAutomaton.{u, v, w} In₁ In₂)
    (hextract :
      PerStrategyWinningFinitePairedPhysicalController.{u, v, x, y, s, w}
        A) :
    ∃ M : LocalSummaryAutomaton.{u, v, w} In₁ In₂,
      M.ReadbackUpgrade (Out₁ := Out₁) (Out₂ := Out₂) A := by
  exact exists_readbackUpgrade_of_finiteGlobalBeliefMachine A fallback
    (perStrategyWinningFiniteGlobalBeliefMachine_of_pairedPhysicalController A
      fallback hextract)

/-- Agreement-form convenience endpoint. -/
theorem exists_readbackUpgrade_of_finitePairedPhysicalControllerAgreement
    (fallback : LocalSummaryAutomaton.{u, v, w} In₁ In₂)
    (hextract :
      PerStrategyWinningFinitePairedPhysicalControllerAgreement.{u, v, x, y,
        s, w} A) :
    ∃ M : LocalSummaryAutomaton.{u, v, w} In₁ In₂,
      M.ReadbackUpgrade (Out₁ := Out₁) (Out₂ := Out₂) A := by
  exact exists_readbackUpgrade_of_finitePairedPhysicalController A fallback
    (perStrategyWinningFinitePairedPhysicalController_of_agreement A hextract)

/-- Physical-regime convenience endpoint.  This is the final consumer for a
controller proved correct by canonical epoch slices rather than by pointwise
agreement with the original strategy. -/
theorem
    exists_readbackUpgrade_of_finitePairedPhysicalControllerPhysicalAcceptance
    (fallback : LocalSummaryAutomaton.{u, v, w} In₁ In₂)
    (hextract :
      PerStrategyWinningFinitePairedPhysicalControllerPhysicalAcceptance.{u,
        v, x, y, s, w} A) :
    ∃ M : LocalSummaryAutomaton.{u, v, w} In₁ In₂,
      M.ReadbackUpgrade (Out₁ := Out₁) (Out₂ := Out₂) A := by
  exact exists_readbackUpgrade_of_finitePairedPhysicalController A fallback
    (perStrategyWinningFinitePairedPhysicalController_of_physicalAcceptance A
      hextract)

end

end DetParityAutomaton

end DistributedSynthesis
