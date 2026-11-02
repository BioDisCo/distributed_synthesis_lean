/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFinitePairedMealyController
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossControllerTraceInvariant

/-!
# Mealy-level trace invariants for the literal-cross controller

The acknowledgement carrier is naturally specified as a Mealy controller:
resolving the old fork determines the current output and the next relay state
in one local transition.  The canonical trace adapter, however, consumes a
Moore physical controller.

This file removes that bookkeeping mismatch.  A concrete construction proves
one invariant on the underlying Mealy controls and, in each graph case, the
exact two outputs emitted by the step.  Mooreization then stores those outputs
in the local controls.  The theorem below turns the Mealy invariant into the
existing `LiteralCrossGraphTraceInvariant` without any further semantic
argument.
-/

namespace DistributedSynthesis

universe u v x y c₁ c₂

namespace FinitePairedMealyController

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (controller : FinitePairedMealyController.{u, v, x, y, c₁, c₂}
    In₁ In₂ Out₁ Out₂)

noncomputable section

/-- Reachable-control and output equations stated directly at Mealy timing.

The proof-side `StateInvariant` may mention a semantic row, selected relay
candidates, acknowledgement correctness, or a schedule index.  None of that
data is added to either executable local control. -/
structure LiteralCrossMealyTraceInvariant
    (env : EnvironmentSequence In₁ In₂) where
  expectedOutputOne : Nat → Out₁
  expectedOutputTwo : Nat → Out₂
  StateInvariant :
    controller.OneControl × controller.TwoControl → Nat → Prop
  initial : StateInvariant (controller.initialOne, controller.initialTwo) 0
  leftStep : ∀ (n : Nat)
      (controls : controller.OneControl × controller.TwoControl),
    StateInvariant controls n → (env n).graph = .left →
      let oneResult := controller.recvOne controls.1 (env n).inputOne
        controls.2 (env n).inputTwo
      let twoResult := controller.noRecvTwo controls.2 (env n).inputTwo
      StateInvariant (oneResult.1, twoResult.1) (n + 1) ∧
        oneResult.2 = expectedOutputOne n ∧
        twoResult.2 = expectedOutputTwo n
  rightStep : ∀ (n : Nat)
      (controls : controller.OneControl × controller.TwoControl),
    StateInvariant controls n → (env n).graph = .right →
      let oneResult := controller.noRecvOne controls.1 (env n).inputOne
      let twoResult := controller.recvTwo controls.2 (env n).inputTwo
        controls.1 (env n).inputOne
      StateInvariant (oneResult.1, twoResult.1) (n + 1) ∧
        oneResult.2 = expectedOutputOne n ∧
        twoResult.2 = expectedOutputTwo n
  bothStep : ∀ (n : Nat)
      (controls : controller.OneControl × controller.TwoControl),
    StateInvariant controls n → (env n).graph = .both →
      let oneResult := controller.recvOne controls.1 (env n).inputOne
        controls.2 (env n).inputTwo
      let twoResult := controller.recvTwo controls.2 (env n).inputTwo
        controls.1 (env n).inputOne
      StateInvariant (oneResult.1, twoResult.1) (n + 1) ∧
        oneResult.2 = expectedOutputOne n ∧
        twoResult.2 = expectedOutputTwo n

namespace LiteralCrossMealyTraceInvariant

/-- Moore-state strengthening of a Mealy invariant.  At time zero the stored
default outputs are irrelevant; at time `n+1` the two stored outputs are
exactly the outputs emitted by Mealy step `n`. -/
def MooreStateInvariant
    [Fintype Out₁] [Fintype Out₂] [Inhabited Out₁] [Inhabited Out₂]
    {env : EnvironmentSequence In₁ In₂}
    (invariant : controller.LiteralCrossMealyTraceInvariant env)
    (controls : (controller.mooreize).OneControl ×
      (controller.mooreize).TwoControl)
    (n : Nat) : Prop :=
  invariant.StateInvariant (controls.1.1, controls.2.1) n ∧
    match n with
    | 0 => True
    | k + 1 =>
        controls.1.2 = invariant.expectedOutputOne k ∧
          controls.2.2 = invariant.expectedOutputTwo k

@[simp] theorem mooreStateInvariant_zero
    [Fintype Out₁] [Fintype Out₂] [Inhabited Out₁] [Inhabited Out₂]
    {env : EnvironmentSequence In₁ In₂}
    (invariant : controller.LiteralCrossMealyTraceInvariant env)
    (controls : (controller.mooreize).OneControl ×
      (controller.mooreize).TwoControl) :
    invariant.MooreStateInvariant controller controls 0 ↔
      invariant.StateInvariant (controls.1.1, controls.2.1) 0 := by
  simp [MooreStateInvariant]

@[simp] theorem mooreStateInvariant_succ
    [Fintype Out₁] [Fintype Out₂] [Inhabited Out₁] [Inhabited Out₂]
    {env : EnvironmentSequence In₁ In₂}
    (invariant : controller.LiteralCrossMealyTraceInvariant env)
    (controls : (controller.mooreize).OneControl ×
      (controller.mooreize).TwoControl)
    (n : Nat) :
    invariant.MooreStateInvariant controller controls (n + 1) ↔
      invariant.StateInvariant (controls.1.1, controls.2.1) (n + 1) ∧
        controls.1.2 = invariant.expectedOutputOne n ∧
        controls.2.2 = invariant.expectedOutputTwo n := by
  simp [MooreStateInvariant]

/-- Convert the four Mealy-level obligations into the exact Moore trace
invariant consumed by the canonical acceptance adapter. -/
noncomputable def toMooreTraceInvariant
    [Fintype Out₁] [Fintype Out₂] [Inhabited Out₁] [Inhabited Out₂]
    {env : EnvironmentSequence In₁ In₂}
    (invariant : controller.LiteralCrossMealyTraceInvariant env) :
    (controller.mooreize).LiteralCrossGraphTraceInvariant env where
  expectedOutputOne := invariant.expectedOutputOne
  expectedOutputTwo := invariant.expectedOutputTwo
  StateInvariant := invariant.MooreStateInvariant controller
  initial := by
    exact ⟨invariant.initial, trivial⟩
  leftStep := by
    intro n controls hstate hgraph
    rcases hstate with ⟨hunderlying, _hstored⟩
    have hstep := invariant.leftStep n
      (controls.1.1, controls.2.1) hunderlying hgraph
    dsimp only at hstep ⊢
    exact ⟨hstep.1, hstep.2⟩
  rightStep := by
    intro n controls hstate hgraph
    rcases hstate with ⟨hunderlying, _hstored⟩
    have hstep := invariant.rightStep n
      (controls.1.1, controls.2.1) hunderlying hgraph
    dsimp only at hstep ⊢
    exact ⟨hstep.1, hstep.2⟩
  bothStep := by
    intro n controls hstate hgraph
    rcases hstate with ⟨hunderlying, _hstored⟩
    have hstep := invariant.bothStep n
      (controls.1.1, controls.2.1) hunderlying hgraph
    dsimp only at hstep ⊢
    exact ⟨hstep.1, hstep.2⟩
  outputs := by
    intro n controls hstate
    exact hstate.2

end LiteralCrossMealyTraceInvariant

end

end FinitePairedMealyController

end DistributedSynthesis
