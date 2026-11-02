/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteGlobalBeliefReadback

/-!
# Finite Mealy emissions as a finite global Moore machine

The model-specific finite recurrence naturally computes the outputs of a
physical round from the control *before* that round and the complete
environment letter.  `FiniteGlobalRoundMachine`, on the other hand, reads a
Moore output from the post-round state.  This file gives the exact timing
adapter: retain the last emitted output pair as two additional finite state
coordinates.

This is a proof-global carrier only.  It gives neither process the other
process's input, a graph orientation, a strict-leader flag, nor a hidden bit.
The generic belief construction still has to prove output uniformity before
the global carrier can be read back as a distributed strategy.
-/

namespace DistributedSynthesis

universe u v w x y

namespace FiniteGlobalRoundMachine

variable {In₁ : Type u} {In₂ : Type v}
variable {Out₁ : Type x} {Out₂ : Type y}

/-! ## The timing adapter -/

/-- Turn a finite Mealy emission on a finite global recurrence into a finite
global Moore machine.  The first coordinate follows `base` literally; the
last two coordinates are exactly the output pair emitted by the latest
transition. -/
noncomputable def withMealyEmission
    (base : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    [Fintype Out₁] [Fintype Out₂] [Inhabited Out₁] [Inhabited Out₂]
    (emit : base.State → EnvironmentRound In₁ In₂ → Out₁ × Out₂) :
    FiniteGlobalRoundMachine.{u, v, max w x y} In₁ In₂ where
  State := base.State × Out₁ × Out₂
  stateFinite := inferInstance
  initial := (base.initial, default, default)
  step := fun state round ↦
    let output := emit state.1 round
    (base.step state.1 round, output.1, output.2)

/-- Process-one Moore projection of `withMealyEmission`. -/
def withMealyEmissionOutputOne
    {base : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
    [Fintype Out₁] [Fintype Out₂] [Inhabited Out₁] [Inhabited Out₂]
    (emit : base.State → EnvironmentRound In₁ In₂ → Out₁ × Out₂) :
    (withMealyEmission base emit).State → Out₁ :=
  fun state ↦ state.2.1

/-- Process-two Moore projection. -/
def withMealyEmissionOutputTwo
    {base : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
    [Fintype Out₁] [Fintype Out₂] [Inhabited Out₁] [Inhabited Out₂]
    (emit : base.State → EnvironmentRound In₁ In₂ → Out₁ × Out₂) :
    (withMealyEmission base emit).State → Out₂ :=
  fun state ↦ state.2.2

@[simp] theorem withMealyEmission_initial_fst
    (base : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    [Fintype Out₁] [Fintype Out₂] [Inhabited Out₁] [Inhabited Out₂]
    (emit : base.State → EnvironmentRound In₁ In₂ → Out₁ × Out₂) :
    (withMealyEmission base emit).initial.1 = base.initial :=
  rfl

@[simp] theorem withMealyEmission_step_fst
    (base : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    [Fintype Out₁] [Fintype Out₂] [Inhabited Out₁] [Inhabited Out₂]
    (emit : base.State → EnvironmentRound In₁ In₂ → Out₁ × Out₂)
    (state : (withMealyEmission base emit).State)
    (round : EnvironmentRound In₁ In₂) :
    ((withMealyEmission base emit).step state round).1 =
      base.step state.1 round :=
  rfl

@[simp] theorem withMealyEmission_step_output
    (base : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    [Fintype Out₁] [Fintype Out₂] [Inhabited Out₁] [Inhabited Out₂]
    (emit : base.State → EnvironmentRound In₁ In₂ → Out₁ × Out₂)
    (state : (withMealyEmission base emit).State)
    (round : EnvironmentRound In₁ In₂) :
    (withMealyEmissionOutputOne emit
        ((withMealyEmission base emit).step state round),
      withMealyEmissionOutputTwo emit
        ((withMealyEmission base emit).step state round)) =
      emit state.1 round := by
  rfl

/-! ## Exact trace equations -/

variable [Fintype In₁] [Fintype In₂]

section
omit [Fintype In₁] [Fintype In₂]

/-- The base coordinate of the lifted state trace is exactly the original
state trace, at every time. -/
theorem withMealyEmission_globalStateTrace_fst
    (base : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    [Fintype Out₁] [Fintype Out₂] [Inhabited Out₁] [Inhabited Out₂]
    (emit : base.State → EnvironmentRound In₁ In₂ → Out₁ × Out₂)
    (env : EnvironmentSequence In₁ In₂) : ∀ n,
    ((withMealyEmission base emit).globalStateTrace env n).1 =
      base.globalStateTrace env n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [globalStateTrace_succ, withMealyEmission_step_fst, ih]

/-- The post-transition Moore projections are exactly the current Mealy
emission. -/
theorem withMealyEmission_globalStateTrace_output
    (base : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    [Fintype Out₁] [Fintype Out₂] [Inhabited Out₁] [Inhabited Out₂]
    (emit : base.State → EnvironmentRound In₁ In₂ → Out₁ × Out₂)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    (withMealyEmissionOutputOne emit
        ((withMealyEmission base emit).globalStateTrace env (n + 1)),
      withMealyEmissionOutputTwo emit
        ((withMealyEmission base emit).globalStateTrace env (n + 1))) =
      emit (base.globalStateTrace env n) (env n) := by
  rw [globalStateTrace_succ, withMealyEmission_step_output,
    withMealyEmission_globalStateTrace_fst]

/-- Pointwise normal form of the lifted physical trace word. -/
theorem withMealyEmission_globalMachineTraceWord_apply
    (base : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    [Fintype Out₁] [Fintype Out₂] [Inhabited Out₁] [Inhabited Out₂]
    (emit : base.State → EnvironmentRound In₁ In₂ → Out₁ × Out₂)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    (withMealyEmission base emit).globalMachineTraceWord
        (withMealyEmissionOutputOne emit)
        (withMealyEmissionOutputTwo emit) env n =
      { inputOne := (env n).inputOne
        inputTwo := (env n).inputTwo
        graph := (env n).graph
        outputOne := (emit (base.globalStateTrace env n) (env n)).1
        outputTwo := (emit (base.globalStateTrace env n) (env n)).2 } := by
  unfold globalMachineTraceWord
  have houtput :
    (withMealyEmissionOutputOne emit
        ((withMealyEmission base emit).globalStateTrace env (n + 1)),
      withMealyEmissionOutputTwo emit
        ((withMealyEmission base emit).globalStateTrace env (n + 1))) =
      emit (base.globalStateTrace env n) (env n) :=
    withMealyEmission_globalStateTrace_output base emit env n
  exact congrArg (fun output : Out₁ × Out₂ ↦
    RoundRecord.mk (env n).inputOne (env n).inputTwo (env n).graph
      output.1 output.2) houtput

/-- Whole-word normal form. -/
theorem withMealyEmission_globalMachineTraceWord_eq
    (base : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    [Fintype Out₁] [Fintype Out₂] [Inhabited Out₁] [Inhabited Out₂]
    (emit : base.State → EnvironmentRound In₁ In₂ → Out₁ × Out₂)
    (env : EnvironmentSequence In₁ In₂) :
    (withMealyEmission base emit).globalMachineTraceWord
        (withMealyEmissionOutputOne emit)
        (withMealyEmissionOutputTwo emit) env =
      fun n ↦
        { inputOne := (env n).inputOne
          inputTwo := (env n).inputTwo
          graph := (env n).graph
          outputOne := (emit (base.globalStateTrace env n) (env n)).1
          outputTwo := (emit (base.globalStateTrace env n) (env n)).2 } := by
  funext n
  exact withMealyEmission_globalMachineTraceWord_apply base emit env n

end

end FiniteGlobalRoundMachine

end DistributedSynthesis
