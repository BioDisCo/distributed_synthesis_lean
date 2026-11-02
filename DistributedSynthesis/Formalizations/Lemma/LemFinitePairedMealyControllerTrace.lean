/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFinitePairedMealyController
import DistributedSynthesis.Formalizations.Lemma.LemFinitePairedPhysicalControllerReadback

/-!
# The semantic control trace of a Mooreized paired Mealy controller

Mooreization stores an endpoint's last emitted output next to its underlying
Mealy control.  This file records the reusable trace fact hidden by that
presentation: at every physical time, the two underlying controls are exactly
the deterministic semantic controls obtained by running the original Mealy
maps.

The theorem is independent of any hierarchy or synthesis construction.  In
particular, it is the generic suffix/reroot bridge used when a controller
enters an absorbing recurrent summand: one first identifies the semantic
control pair and then uses the ordinary finite-global-machine reroot theorem.
-/

namespace DistributedSynthesis

universe u v x y c₁ c₂

namespace FinitePairedMealyController

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable (controller : FinitePairedMealyController.{u, v, x, y, c₁, c₂}
  In₁ In₂ Out₁ Out₂)

noncomputable section

variable [Fintype In₁] [Fintype In₂]
variable [Fintype Out₁] [Fintype Out₂]
variable [Inhabited Out₁] [Inhabited Out₂]

/-- Underlying-control update performed by the paired Mealy maps.  A
simultaneous round applies both receive maps to the same pre-round pair. -/
def semanticAdvanceControls
    (controls : controller.OneControl × controller.TwoControl)
    (round : EnvironmentRound In₁ In₂) :
    controller.OneControl × controller.TwoControl :=
  match round.graph with
  | .left =>
      ((controller.recvOne controls.1 round.inputOne controls.2
        round.inputTwo).1,
        (controller.noRecvTwo controls.2 round.inputTwo).1)
  | .right =>
      ((controller.noRecvOne controls.1 round.inputOne).1,
        (controller.recvTwo controls.2 round.inputTwo controls.1
          round.inputOne).1)
  | .both =>
      ((controller.recvOne controls.1 round.inputOne controls.2
        round.inputTwo).1,
        (controller.recvTwo controls.2 round.inputTwo controls.1
          round.inputOne).1)

/-- The two underlying Mealy controls before physical round `n`. -/
def semanticControlTrace (env : EnvironmentSequence In₁ In₂) : Nat →
    controller.OneControl × controller.TwoControl
  | 0 => (controller.initialOne, controller.initialTwo)
  | n + 1 => controller.semanticAdvanceControls
      (semanticControlTrace env n) (env n)

section
omit [Fintype In₁] [Fintype In₂]

/-- Forgetting the stored Moore outputs commutes with one physical update. -/
theorem mooreize_advanceControls_underlying
    (state : (controller.mooreize).OneControl ×
      (controller.mooreize).TwoControl)
    (round : EnvironmentRound In₁ In₂) :
    let next := (controller.mooreize).advanceControls state round
    (next.1.1, next.2.1) =
      controller.semanticAdvanceControls (state.1.1, state.2.1) round := by
  cases hgraph : round.graph <;>
    simp [FinitePairedPhysicalController.advanceControls,
      semanticAdvanceControls, hgraph, FinitePairedMealyController.mooreize]

/-- Projecting away the stored Moore outputs from the actual global state
trace gives the literal semantic Mealy control trace. -/
theorem mooreize_globalStateTrace_underlying
    (env : EnvironmentSequence In₁ In₂) : ∀ n : Nat,
    let state := (controller.mooreize).globalMachine.globalStateTrace env n
    (state.1.1, state.2.1) = controller.semanticControlTrace env n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [FiniteGlobalRoundMachine.globalStateTrace_succ]
      change
        let state := (controller.mooreize).advanceControls
          ((controller.mooreize).globalMachine.globalStateTrace env n) (env n)
        (state.1.1, state.2.1) = controller.semanticControlTrace env (n + 1)
      dsimp only
      rw [controller.mooreize_advanceControls_underlying]
      simp only [semanticControlTrace]
      rw [ih]

/-- Component form for process one. -/
theorem mooreize_globalStateTrace_underlying_one
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    ((controller.mooreize).globalMachine.globalStateTrace env n).1.1 =
      (controller.semanticControlTrace env n).1 := by
  exact congrArg Prod.fst
    (controller.mooreize_globalStateTrace_underlying env n)

/-- Component form for process two. -/
theorem mooreize_globalStateTrace_underlying_two
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    ((controller.mooreize).globalMachine.globalStateTrace env n).2.1 =
      (controller.semanticControlTrace env n).2 := by
  exact congrArg Prod.snd
    (controller.mooreize_globalStateTrace_underlying env n)

end

end

end FinitePairedMealyController

end DistributedSynthesis
