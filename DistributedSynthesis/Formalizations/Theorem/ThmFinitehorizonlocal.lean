/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Definition.DefSynthesisProblem
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod

/-!
# Finite-horizon local synthesis

This file formalizes the finite-search content of `thm:finitehorizonlocal`.
For a fixed horizon, the reachable local views form finite carriers. Local
strategies are therefore finite functions from those local carriers to the
output alphabets, and the finite environment-prefix space can be checked
exhaustively against a deterministic terminal monitor.
-/

namespace DistributedSynthesis

universe u v x y a b

/-- A finite local strategy table for the two processes at a fixed horizon. -/
abbrev FiniteLocalStrategy
    (ViewOne : Type u) (ViewTwo : Type v)
    (Out₁ : Type x) (Out₂ : Type y) :=
  (ViewOne -> Out₁) × (ViewTwo -> Out₂)

/--
Finite horizon-local synthesis problem.  The type `EnvPrefix` represents all
environment words of the fixed horizon; `ViewOne` and `ViewTwo` are the finite
sets of local views relevant up to that horizon; `terminal` is the deterministic
monitor state after simulating the horizon under a local strategy table.
-/
structure FiniteHorizonLocalProblem
    (Out₁ : Type x) (Out₂ : Type y) where
  EnvPrefix : Type u
  envPrefixFinite : Fintype EnvPrefix
  ViewOne : Type v
  viewOneFinite : Fintype ViewOne
  ViewTwo : Type a
  viewTwoFinite : Fintype ViewTwo
  State : Type b
  terminal :
    FiniteLocalStrategy ViewOne ViewTwo Out₁ Out₂ ->
      EnvPrefix ->
        State
  accept : State -> Prop
  acceptDecidable : (state : State) -> Decidable (accept state)

attribute [instance] FiniteHorizonLocalProblem.envPrefixFinite
attribute [instance] FiniteHorizonLocalProblem.viewOneFinite
attribute [instance] FiniteHorizonLocalProblem.viewTwoFinite
attribute [instance] FiniteHorizonLocalProblem.acceptDecidable

namespace FiniteHorizonLocalProblem

/-- Strategy tables available in the finite horizon-local problem. -/
abbrev Strategy
    {Out₁ : Type x} {Out₂ : Type y}
    (P : FiniteHorizonLocalProblem.{u, v, x, y, a, b} Out₁ Out₂) :=
  FiniteLocalStrategy P.ViewOne P.ViewTwo Out₁ Out₂

/-- A finite local strategy wins iff all fixed-horizon environment prefixes are accepted. -/
def Wins
    {Out₁ : Type x} {Out₂ : Type y}
    (P : FiniteHorizonLocalProblem.{u, v, x, y, a, b} Out₁ Out₂)
    (strategy : P.Strategy) :
    Prop :=
  ∀ envPrefix : P.EnvPrefix, P.accept (P.terminal strategy envPrefix)

/-- The finite-horizon local synthesis question. -/
def Solvable
    {Out₁ : Type x} {Out₂ : Type y}
    (P : FiniteHorizonLocalProblem.{u, v, x, y, a, b} Out₁ Out₂) :
    Prop :=
  ∃ strategy : P.Strategy, P.Wins strategy

/-- The finite strategy-table carrier is finite. -/
theorem finite_local_strategy_space
    {Out₁ : Type x} {Out₂ : Type y}
    [Fintype Out₁] [Fintype Out₂]
    (P : FiniteHorizonLocalProblem.{u, v, x, y, a, b} Out₁ Out₂) :
    Nonempty (Fintype P.Strategy) := by
  classical
  haveI : Fintype P.ViewOne := P.viewOneFinite
  haveI : Fintype P.ViewTwo := P.viewTwoFinite
  change Nonempty (Fintype ((P.ViewOne -> Out₁) × (P.ViewTwo -> Out₂)))
  exact ⟨inferInstance⟩

/-- Winning of a fixed strategy is a decidable finite universal check. -/
noncomputable def wins_decidable
    {Out₁ : Type x} {Out₂ : Type y}
    (P : FiniteHorizonLocalProblem.{u, v, x, y, a, b} Out₁ Out₂)
    (strategy : P.Strategy) :
    Decidable (P.Wins strategy) := by
  haveI : Fintype P.EnvPrefix := P.envPrefixFinite
  haveI : (state : P.State) -> Decidable (P.accept state) := P.acceptDecidable
  unfold Wins
  infer_instance

/--
Theorem `thm:finitehorizonlocal`: finite-horizon local synthesis reduces to
finite enumeration of local strategy tables and finite checking of all
environment prefixes.
-/
noncomputable def finite_horizon_local_synthesis_decidable
    {Out₁ : Type x} {Out₂ : Type y}
    [Fintype Out₁] [Fintype Out₂]
    (P : FiniteHorizonLocalProblem.{u, v, x, y, a, b} Out₁ Out₂) :
    Decidable P.Solvable := by
  haveI : Fintype P.Strategy := (finite_local_strategy_space P).some
  haveI : (strategy : P.Strategy) -> Decidable (P.Wins strategy) :=
    P.wins_decidable
  unfold Solvable
  infer_instance

/-- The decision problem is exactly the paper's finite exhaustive test. -/
theorem finite_horizon_local_finite_test_exact
    {Out₁ : Type x} {Out₂ : Type y}
    (P : FiniteHorizonLocalProblem.{u, v, x, y, a, b} Out₁ Out₂) :
    P.Solvable ↔
      ∃ strategy : P.Strategy,
        ∀ envPrefix : P.EnvPrefix,
          P.accept (P.terminal strategy envPrefix) := by
  rfl

end FiniteHorizonLocalProblem

end DistributedSynthesis
