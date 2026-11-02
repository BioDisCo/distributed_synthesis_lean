/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmAutomataBackend
import DistributedSynthesis.Formalizations.Theorem.ThmLTLtoDPA

/-!
# From LTL formulas to effective parity specifications

This file connects the reusable LTL/DPA interface to the synthesis theorem's
`EffectiveParitySpecification` boundary.  The remaining paper-specific
compilation step is the finite dynamic-hierarchy parity-game construction for
the compiled DPA; once supplied, the LTL specification is in the scope of the
verified main theorem.
-/

namespace DistributedSynthesis

universe u v x y ap a b aut

/--
A complete certificate that an LTL formula over round records has been compiled
through a deterministic parity automaton into a finite dynamic-hierarchy game.
-/
structure LTLFiniteGameCompilation
    (AP : Type ap)
    (In₁ : Type u)
    (In₂ : Type v)
    (Out₁ : Type x)
    (Out₂ : Type y)
    [DecidableEq AP] where
  compiler :
    LTLToDPACompiler.{ap, max u v x y, aut}
      AP
      (RoundRecord In₁ In₂ Graph Out₁ Out₂)
  formula : LTL AP
  finiteGame : FiniteDynamicHierarchyParityGame.{a, b}
  finiteGameRealizableIff :
    finiteGame.realizable ↔
      ∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          (compiler.compile formula).Accepts (execution σ env)

/-- The semantic LTL predicate induced by a finite-game compilation certificate. -/
def LTLFiniteGameCompilation.predicate
    {AP : Type ap}
    {In₁ : Type u}
    {In₂ : Type v}
    {Out₁ : Type x}
    {Out₂ : Type y}
    [DecidableEq AP]
    (cert : LTLFiniteGameCompilation.{u, v, x, y, ap, a, b, aut}
      AP In₁ In₂ Out₁ Out₂) :
    Specification In₁ In₂ Out₁ Out₂ :=
  fun word => LTL.Satisfies cert.compiler.interp word cert.formula

/--
Package the canonical LTL finite-game certificate from the DPA backend
certificate for the automaton produced by the compiler.
-/
def LTLFiniteGameCompilation.ofDPAGameCompilation
    {AP : Type ap}
    {In₁ : Type u}
    {In₂ : Type v}
    {Out₁ : Type x}
    {Out₂ : Type y}
    [DecidableEq AP]
    (compiler :
      LTLToDPACompiler.{ap, max u v x y, aut}
        AP
        (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (formula : LTL AP)
    (gameCompilation :
      DPAToFiniteGameCompilation.{u, v, x, y, a}
        Out₂
        (compiler.compile formula)) :
    LTLFiniteGameCompilation.{u, v, x, y, ap, a, max u v x y, aut}
      AP In₁ In₂ Out₁ Out₂ where
  compiler := compiler
  formula := formula
  finiteGame := gameCompilation.finiteGame
  finiteGameRealizableIff := gameCompilation.realizabilityEquivalent

/--
Package the canonical LTL finite-game certificate using a uniform finite-game
compiler for all DPA objectives over round records.
-/
def LTLFiniteGameCompilation.ofDPAFiniteGameCompiler
    {AP : Type ap}
    {In₁ : Type u}
    {In₂ : Type v}
    {Out₁ : Type x}
    {Out₂ : Type y}
    [DecidableEq AP]
    (compiler :
      LTLToDPACompiler.{ap, max u v x y, aut}
        AP
        (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (formula : LTL AP)
    (gameCompiler :
      DPAFiniteGameCompiler.{u, v, x, y, a} In₁ In₂ Out₁ Out₂) :
    LTLFiniteGameCompilation.{u, v, x, y, ap, a, max u v x y, aut}
      AP In₁ In₂ Out₁ Out₂ :=
  LTLFiniteGameCompilation.ofDPAGameCompilation
    compiler formula (gameCompiler.compile (compiler.compile formula))

/--
Package an LTL finite-game certificate for the priority-normalized compiler
from a finite-game compilation of the original compiler output.
-/
def LTLFiniteGameCompilation.ofDPAGameCompilationShiftPriorityTwo
    {AP : Type ap}
    {In₁ : Type u}
    {In₂ : Type v}
    {Out₁ : Type x}
    {Out₂ : Type y}
    [DecidableEq AP]
    (compiler :
      LTLToDPACompiler.{ap, max u v x y, aut}
        AP
        (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (formula : LTL AP)
    (gameCompilation :
      DPAToFiniteGameCompilation.{u, v, x, y, a}
        Out₂
        (compiler.compile formula)) :
    LTLFiniteGameCompilation.{u, v, x, y, ap, a, max u v x y, aut}
      AP In₁ In₂ Out₁ Out₂ :=
  LTLFiniteGameCompilation.ofDPAGameCompilation
    compiler.shiftPriorityTwo formula gameCompilation.shiftPriorityTwo

/--
Package an LTL finite-game certificate from a tracking-style DPA backend
certificate for the automaton produced by the compiler.
-/
def LTLFiniteGameCompilation.ofDPATrackingGameCompilation
    {AP : Type ap}
    {In₁ : Type u}
    {In₂ : Type v}
    {Out₁ : Type x}
    {Out₂ : Type y}
    [DecidableEq AP]
    (compiler :
      LTLToDPACompiler.{ap, max u v x y, aut}
        AP
        (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (formula : LTL AP)
    (gameCompilation :
      DPATrackingFiniteGameCompilation.{u, v, x, y, a}
        Out₂
        (compiler.compile formula)) :
    LTLFiniteGameCompilation.{u, v, x, y, ap, a, max u v x y, aut}
      AP In₁ In₂ Out₁ Out₂ :=
  LTLFiniteGameCompilation.ofDPAGameCompilation
    compiler formula gameCompilation.toDPAToFiniteGameCompilation

/--
Package an LTL finite-game certificate using a uniform tracking-style
finite-game compiler for all DPA objectives over round records.
-/
def LTLFiniteGameCompilation.ofDPATrackingFiniteGameCompiler
    {AP : Type ap}
    {In₁ : Type u}
    {In₂ : Type v}
    {Out₁ : Type x}
    {Out₂ : Type y}
    [DecidableEq AP]
    (compiler :
      LTLToDPACompiler.{ap, max u v x y, aut}
        AP
        (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (formula : LTL AP)
    (gameCompiler :
      DPATrackingFiniteGameCompiler.{u, v, x, y, a} In₁ In₂ Out₁ Out₂) :
    LTLFiniteGameCompilation.{u, v, x, y, ap, a, max u v x y, aut}
      AP In₁ In₂ Out₁ Out₂ :=
  LTLFiniteGameCompilation.ofDPATrackingGameCompilation
    compiler formula (gameCompiler.compile (compiler.compile formula))

/--
Package an LTL finite-game certificate for the priority-normalized compiler
from a tracking-style finite-game compilation of the original compiler output.
-/
def LTLFiniteGameCompilation.ofDPATrackingGameCompilationShiftPriorityTwo
    {AP : Type ap}
    {In₁ : Type u}
    {In₂ : Type v}
    {Out₁ : Type x}
    {Out₂ : Type y}
    [DecidableEq AP]
    (compiler :
      LTLToDPACompiler.{ap, max u v x y, aut}
        AP
        (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (formula : LTL AP)
    (gameCompilation :
      DPATrackingFiniteGameCompilation.{u, v, x, y, a}
        Out₂
        (compiler.compile formula)) :
    LTLFiniteGameCompilation.{u, v, x, y, ap, a, max u v x y, aut}
      AP In₁ In₂ Out₁ Out₂ :=
  LTLFiniteGameCompilation.ofDPATrackingGameCompilation
    compiler.shiftPriorityTwo formula gameCompilation.shiftPriorityTwo

/--
Turn a complete LTL/DPA/finite-game compilation certificate into the effective
parity specification consumed by `thm:main`.
-/
def LTLFiniteGameCompilation.toEffectiveParitySpecification
    {AP : Type ap}
    {In₁ : Type u}
    {In₂ : Type v}
    {Out₁ : Type x}
    {Out₂ : Type y}
    [DecidableEq AP]
    (cert : LTLFiniteGameCompilation.{u, v, x, y, ap, a, b, aut}
      AP In₁ In₂ Out₁ Out₂) :
    EffectiveParitySpecification.{u, v, x, y, a, b} In₁ In₂ Out₁ Out₂ where
  predicate := cert.predicate
  finiteGame := cert.finiteGame
  realizabilityEquivalent := by
    rw [cert.finiteGameRealizableIff]
    constructor
    · intro h
      rcases h with ⟨σ, hσ⟩
      exact ⟨σ, fun env => (cert.compiler.correct cert.formula (execution σ env)).mp (hσ env)⟩
    · intro h
      rcases h with ⟨σ, hσ⟩
      exact ⟨σ, fun env => (cert.compiler.correct cert.formula (execution σ env)).mpr (hσ env)⟩

/-- LTL synthesis is decidable once the two compilation certificates are supplied. -/
noncomputable def ltl_compiled_synthesis_problem_decidable
    {AP : Type ap}
    {In₁ : Type u}
    {In₂ : Type v}
    {Out₁ : Type x}
    {Out₂ : Type y}
    [DecidableEq AP]
    (cert : LTLFiniteGameCompilation.{u, v, x, y, ap, a, b, aut}
      AP In₁ In₂ Out₁ Out₂) :
    Decidable (SynthesisProblem cert.predicate) :=
  effective_parity_synthesis_problem_decidable cert.toEffectiveParitySpecification

/-!
The following direct bridge is the canonical route used by the main theorem:
an LTL-to-DPA compiler plus the finite-game compilation for the compiled DPA
is enough to produce an effective parity specification with the original LTL
semantics as its predicate.
-/

/-- Directly build the effective parity specification for an LTL formula. -/
def LTLToDPACompiler.toEffectiveParitySpecification
    {AP : Type ap}
    {In₁ : Type u}
    {In₂ : Type v}
    {Out₁ : Type x}
    {Out₂ : Type y}
    [DecidableEq AP]
    (compiler :
      LTLToDPACompiler.{ap, max u v x y, aut}
        AP
        (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (formula : LTL AP)
    (gameCompilation :
      DPAToFiniteGameCompilation.{u, v, x, y, a}
        Out₂
        (compiler.compile formula)) :
    EffectiveParitySpecification.{u, v, x, y, a, max u v x y}
      In₁ In₂ Out₁ Out₂ :=
  (LTLFiniteGameCompilation.ofDPAGameCompilation compiler formula gameCompilation)
    |>.toEffectiveParitySpecification

/--
Directly build the effective parity specification for an LTL formula from a
uniform finite-game compiler for DPA objectives.
-/
def LTLToDPACompiler.toEffectiveParitySpecificationFromDPACompiler
    {AP : Type ap}
    {In₁ : Type u}
    {In₂ : Type v}
    {Out₁ : Type x}
    {Out₂ : Type y}
    [DecidableEq AP]
    (compiler :
      LTLToDPACompiler.{ap, max u v x y, aut}
        AP
        (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (formula : LTL AP)
    (gameCompiler :
      DPAFiniteGameCompiler.{u, v, x, y, a} In₁ In₂ Out₁ Out₂) :
    EffectiveParitySpecification.{u, v, x, y, a, max u v x y}
      In₁ In₂ Out₁ Out₂ :=
  (LTLFiniteGameCompilation.ofDPAFiniteGameCompiler compiler formula gameCompiler)
    |>.toEffectiveParitySpecification

/--
Directly build the effective parity specification for an LTL formula from a
tracking-style DPA finite-game compilation.
-/
def LTLToDPACompiler.toEffectiveParitySpecificationFromTracking
    {AP : Type ap}
    {In₁ : Type u}
    {In₂ : Type v}
    {Out₁ : Type x}
    {Out₂ : Type y}
    [DecidableEq AP]
    (compiler :
      LTLToDPACompiler.{ap, max u v x y, aut}
        AP
        (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (formula : LTL AP)
    (gameCompilation :
      DPATrackingFiniteGameCompilation.{u, v, x, y, a}
        Out₂
        (compiler.compile formula)) :
    EffectiveParitySpecification.{u, v, x, y, a, max u v x y}
      In₁ In₂ Out₁ Out₂ :=
  (LTLFiniteGameCompilation.ofDPATrackingGameCompilation compiler formula gameCompilation)
    |>.toEffectiveParitySpecification

/--
Directly build the effective parity specification for an LTL formula from a
uniform tracking-style finite-game compiler for DPA objectives.
-/
def LTLToDPACompiler.toEffectiveParitySpecificationFromTrackingCompiler
    {AP : Type ap}
    {In₁ : Type u}
    {In₂ : Type v}
    {Out₁ : Type x}
    {Out₂ : Type y}
    [DecidableEq AP]
    (compiler :
      LTLToDPACompiler.{ap, max u v x y, aut}
        AP
        (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (formula : LTL AP)
    (gameCompiler :
      DPATrackingFiniteGameCompiler.{u, v, x, y, a} In₁ In₂ Out₁ Out₂) :
    EffectiveParitySpecification.{u, v, x, y, a, max u v x y}
      In₁ In₂ Out₁ Out₂ :=
  (LTLFiniteGameCompilation.ofDPATrackingFiniteGameCompiler
      compiler formula gameCompiler)
    |>.toEffectiveParitySpecification

/--
Directly build the effective parity specification for an LTL formula from the
paper-facing rotating rational-run epoch compiler.
-/
noncomputable def LTLToDPACompiler.toEffectiveParitySpecificationFromRationalRunCompiler
    {AP : Type ap}
    {In₁ : Type u}
    {In₂ : Type v}
    {Out₁ : Type x}
    {Out₂ : Type y}
    [DecidableEq AP]
    [Inhabited In₁]
    [Inhabited In₂]
    [Fintype In₁]
    [Fintype In₂]
    [Fintype Out₁]
    [Fintype Out₂]
    (compiler :
      LTLToDPACompiler.{ap, max u v x y, aut}
        AP
        (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (formula : LTL AP)
    (gameCompiler :
      DPARotatingRationalRunEpochCompiler.{u, v, x, y, ap, a, b, aut}
        In₁ In₂ Out₁ Out₂) :
    EffectiveParitySpecification.{u, v, x, y, max u v x y, max u v x y}
      In₁ In₂ Out₁ Out₂ :=
  compiler.toEffectiveParitySpecificationFromDPACompiler
    formula gameCompiler.toDPAFiniteGameCompiler

/--
Tracking-style variant of
`LTLToDPACompiler.toEffectiveParitySpecificationFromRationalRunCompiler`.
The rotating rational-run compiler is viewed as a zero-prefix tracking compiler.
-/
noncomputable def LTLToDPACompiler.toEffectiveParitySpecificationFromRationalRunTrackingCompiler
    {AP : Type ap}
    {In₁ : Type u}
    {In₂ : Type v}
    {Out₁ : Type x}
    {Out₂ : Type y}
    [DecidableEq AP]
    [Inhabited In₁]
    [Inhabited In₂]
    [Fintype In₁]
    [Fintype In₂]
    [Fintype Out₁]
    [Fintype Out₂]
    (compiler :
      LTLToDPACompiler.{ap, max u v x y, aut}
        AP
        (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (formula : LTL AP)
    (gameCompiler :
      DPARotatingRationalRunEpochCompiler.{u, v, x, y, ap, a, b, aut}
        In₁ In₂ Out₁ Out₂) :
    EffectiveParitySpecification.{u, v, x, y, max u v x y, max u v x y}
      In₁ In₂ Out₁ Out₂ :=
  compiler.toEffectiveParitySpecificationFromTrackingCompiler
    formula gameCompiler.toDPATrackingFiniteGameCompiler

/--
LTL synthesis is decidable from the canonical pair of backend certificates:
the reusable LTL-to-DPA compiler and the finite-game compilation of the
compiled DPA.
-/
noncomputable def ltl_dpa_compiled_synthesis_problem_decidable
    {AP : Type ap}
    {In₁ : Type u}
    {In₂ : Type v}
    {Out₁ : Type x}
    {Out₂ : Type y}
    [DecidableEq AP]
    (compiler :
      LTLToDPACompiler.{ap, max u v x y, aut}
        AP
        (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (formula : LTL AP)
    (gameCompilation :
      DPAToFiniteGameCompilation.{u, v, x, y, a}
        Out₂
        (compiler.compile formula)) :
    Decidable
      (SynthesisProblem
        (fun word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂) =>
          LTL.Satisfies compiler.interp word formula)) :=
  ltl_compiled_synthesis_problem_decidable
    (LTLFiniteGameCompilation.ofDPAGameCompilation compiler formula gameCompilation)

/--
LTL synthesis is decidable from an LTL-to-DPA compiler and a tracking-style
finite-game compilation of the compiled DPA.
-/
noncomputable def ltl_dpa_tracking_compiled_synthesis_problem_decidable
    {AP : Type ap}
    {In₁ : Type u}
    {In₂ : Type v}
    {Out₁ : Type x}
    {Out₂ : Type y}
    [DecidableEq AP]
    (compiler :
      LTLToDPACompiler.{ap, max u v x y, aut}
        AP
        (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (formula : LTL AP)
    (gameCompilation :
      DPATrackingFiniteGameCompilation.{u, v, x, y, a}
        Out₂
        (compiler.compile formula)) :
    Decidable
      (SynthesisProblem
        (fun word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂) =>
          LTL.Satisfies compiler.interp word formula)) :=
  ltl_compiled_synthesis_problem_decidable
    (LTLFiniteGameCompilation.ofDPATrackingGameCompilation
      compiler formula gameCompilation)

/--
LTL synthesis is decidable from an LTL-to-DPA compiler and a uniform
finite-game compiler for DPA objectives.
-/
noncomputable def ltl_dpa_compiler_synthesis_problem_decidable
    {AP : Type ap}
    {In₁ : Type u}
    {In₂ : Type v}
    {Out₁ : Type x}
    {Out₂ : Type y}
    [DecidableEq AP]
    (compiler :
      LTLToDPACompiler.{ap, max u v x y, aut}
        AP
        (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (formula : LTL AP)
    (gameCompiler :
      DPAFiniteGameCompiler.{u, v, x, y, a} In₁ In₂ Out₁ Out₂) :
    Decidable
      (SynthesisProblem
        (fun word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂) =>
          LTL.Satisfies compiler.interp word formula)) :=
  ltl_compiled_synthesis_problem_decidable
    (LTLFiniteGameCompilation.ofDPAFiniteGameCompiler
      compiler formula gameCompiler)

/--
LTL synthesis is decidable from an LTL-to-DPA compiler and a uniform
tracking-style finite-game compiler for DPA objectives.
-/
noncomputable def ltl_dpa_tracking_compiler_synthesis_problem_decidable
    {AP : Type ap}
    {In₁ : Type u}
    {In₂ : Type v}
    {Out₁ : Type x}
    {Out₂ : Type y}
    [DecidableEq AP]
    (compiler :
      LTLToDPACompiler.{ap, max u v x y, aut}
        AP
        (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (formula : LTL AP)
    (gameCompiler :
      DPATrackingFiniteGameCompiler.{u, v, x, y, a} In₁ In₂ Out₁ Out₂) :
    Decidable
      (SynthesisProblem
        (fun word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂) =>
          LTL.Satisfies compiler.interp word formula)) :=
  ltl_compiled_synthesis_problem_decidable
    (LTLFiniteGameCompilation.ofDPATrackingFiniteGameCompiler
      compiler formula gameCompiler)

/--
LTL synthesis is decidable from an LTL-to-DPA compiler and the paper-facing
rotating rational-run epoch compiler.
-/
noncomputable def ltl_dpa_rational_run_compiler_synthesis_problem_decidable
    {AP : Type ap}
    {In₁ : Type u}
    {In₂ : Type v}
    {Out₁ : Type x}
    {Out₂ : Type y}
    [DecidableEq AP]
    [Inhabited In₁]
    [Inhabited In₂]
    [Fintype In₁]
    [Fintype In₂]
    [Fintype Out₁]
    [Fintype Out₂]
    (compiler :
      LTLToDPACompiler.{ap, max u v x y, aut}
        AP
        (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (formula : LTL AP)
    (gameCompiler :
      DPARotatingRationalRunEpochCompiler.{u, v, x, y, ap, a, b, aut}
        In₁ In₂ Out₁ Out₂) :
    Decidable
      (SynthesisProblem
        (fun word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂) =>
          LTL.Satisfies compiler.interp word formula)) :=
  ltl_dpa_compiler_synthesis_problem_decidable
    compiler formula gameCompiler.toDPAFiniteGameCompiler

/--
Muller-backed LTL blocks plus a uniform finite-game compiler already reach the
effective parity specification boundary used by the main theorem.
-/
def LTLDPAMullerBuildingBlocks.toEffectiveParitySpecification
    {AP : Type ap}
    {In₁ : Type u}
    {In₂ : Type v}
    {Out₁ : Type x}
    {Out₂ : Type y}
    [DecidableEq AP]
    (blocks :
      LTLDPAMullerBuildingBlocks.{ap, max u v x y, aut}
        AP
        (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (formula : LTL AP)
    (gameCompiler :
      DPAFiniteGameCompiler.{u, v, x, y, a} In₁ In₂ Out₁ Out₂) :
    EffectiveParitySpecification.{u, v, x, y, a, max u v x y}
      In₁ In₂ Out₁ Out₂ :=
  blocks.toCompiler.toEffectiveParitySpecificationFromDPACompiler
    formula gameCompiler

/--
Muller-backed LTL blocks plus a uniform tracking-style finite-game compiler
also reach the effective parity specification boundary used by the main
theorem.
-/
def LTLDPAMullerBuildingBlocks.toEffectiveParitySpecificationFromTrackingCompiler
    {AP : Type ap}
    {In₁ : Type u}
    {In₂ : Type v}
    {Out₁ : Type x}
    {Out₂ : Type y}
    [DecidableEq AP]
    (blocks :
      LTLDPAMullerBuildingBlocks.{ap, max u v x y, aut}
        AP
        (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (formula : LTL AP)
    (gameCompiler :
      DPATrackingFiniteGameCompiler.{u, v, x, y, a} In₁ In₂ Out₁ Out₂) :
    EffectiveParitySpecification.{u, v, x, y, a, max u v x y}
      In₁ In₂ Out₁ Out₂ :=
  blocks.toCompiler.toEffectiveParitySpecificationFromTrackingCompiler
    formula gameCompiler

/--
LTL blocks whose Boolean closure is supplied by the proved LAR
Muller-to-DPA construction, plus a uniform finite-game compiler, reach the
effective parity boundary directly.
-/
noncomputable def LTLFormulaDPACompilation.toEffectiveParitySpecificationOfLAR
    {AP : Type ap}
    {In₁ : Type u}
    {In₂ : Type v}
    {Out₁ : Type x}
    {Out₂ : Type y}
    [DecidableEq AP]
    (interp : AP -> RoundRecord In₁ In₂ Graph Out₁ Out₂ -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (untilC :
      ∀ {φ ψ : LTL AP},
        LTLFormulaDPACompilation.{ap, max u v x y, aut} interp φ ->
        LTLFormulaDPACompilation.{ap, max u v x y, aut} interp ψ ->
          LTLFormulaDPACompilation.{ap, max u v x y, aut} interp (LTL.until φ ψ))
    (releaseC :
      ∀ {φ ψ : LTL AP},
        LTLFormulaDPACompilation.{ap, max u v x y, aut} interp φ ->
        LTLFormulaDPACompilation.{ap, max u v x y, aut} interp ψ ->
          LTLFormulaDPACompilation.{ap, max u v x y, aut} interp (LTL.release φ ψ))
    (formula : LTL AP)
    (gameCompiler :
      DPAFiniteGameCompiler.{u, v, x, y, a} In₁ In₂ Out₁ Out₂) :
    EffectiveParitySpecification.{u, v, x, y, a, max u v x y}
      In₁ In₂ Out₁ Out₂ :=
  (LTLDPAMullerBuildingBlocks.ofLAR interp dec untilC releaseC)
    |>.toEffectiveParitySpecification formula gameCompiler

/--
Tracking-style finite-game variant of
`LTLFormulaDPACompilation.toEffectiveParitySpecificationOfLAR`.
-/
noncomputable def LTLFormulaDPACompilation.toEffectiveParitySpecificationOfLARFromTracking
    {AP : Type ap}
    {In₁ : Type u}
    {In₂ : Type v}
    {Out₁ : Type x}
    {Out₂ : Type y}
    [DecidableEq AP]
    (interp : AP -> RoundRecord In₁ In₂ Graph Out₁ Out₂ -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (untilC :
      ∀ {φ ψ : LTL AP},
        LTLFormulaDPACompilation.{ap, max u v x y, aut} interp φ ->
        LTLFormulaDPACompilation.{ap, max u v x y, aut} interp ψ ->
          LTLFormulaDPACompilation.{ap, max u v x y, aut} interp (LTL.until φ ψ))
    (releaseC :
      ∀ {φ ψ : LTL AP},
        LTLFormulaDPACompilation.{ap, max u v x y, aut} interp φ ->
        LTLFormulaDPACompilation.{ap, max u v x y, aut} interp ψ ->
          LTLFormulaDPACompilation.{ap, max u v x y, aut} interp (LTL.release φ ψ))
    (formula : LTL AP)
    (gameCompiler :
      DPATrackingFiniteGameCompiler.{u, v, x, y, a} In₁ In₂ Out₁ Out₂) :
    EffectiveParitySpecification.{u, v, x, y, a, max u v x y}
      In₁ In₂ Out₁ Out₂ :=
  (LTLDPAMullerBuildingBlocks.ofLAR interp dec untilC releaseC)
    |>.toEffectiveParitySpecificationFromTrackingCompiler formula gameCompiler

/--
Until-only LTL blocks, with generic constants and decidable atomic
interpretations, Boolean closure from LAR, and release by duality, reach the
effective parity boundary directly.
-/
noncomputable def LTLFormulaDPACompilation.toEffectiveParitySpecificationOfUntilLAR
    {AP : Type ap}
    {In₁ : Type u}
    {In₂ : Type v}
    {Out₁ : Type x}
    {Out₂ : Type y}
    [DecidableEq AP]
    (interp : AP -> RoundRecord In₁ In₂ Graph Out₁ Out₂ -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (untilC :
      ∀ {φ ψ : LTL AP},
        LTLFormulaDPACompilation.{ap, max u v x y, aut} interp φ ->
        LTLFormulaDPACompilation.{ap, max u v x y, aut} interp ψ ->
          LTLFormulaDPACompilation.{ap, max u v x y, aut} interp (LTL.until φ ψ))
    (formula : LTL AP)
    (gameCompiler :
      DPAFiniteGameCompiler.{u, v, x, y, a} In₁ In₂ Out₁ Out₂) :
    EffectiveParitySpecification.{u, v, x, y, a, max u v x y}
      In₁ In₂ Out₁ Out₂ :=
  (LTLDPAUntilMullerBuildingBlocks.ofLAR interp dec untilC)
    |>.toMullerBuildingBlocks.toEffectiveParitySpecification formula gameCompiler

/--
Tracking-style finite-game variant of the until-only LAR LTL route.
-/
noncomputable def LTLFormulaDPACompilation.toEffectiveParitySpecificationOfUntilLARFromTracking
    {AP : Type ap}
    {In₁ : Type u}
    {In₂ : Type v}
    {Out₁ : Type x}
    {Out₂ : Type y}
    [DecidableEq AP]
    (interp : AP -> RoundRecord In₁ In₂ Graph Out₁ Out₂ -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (untilC :
      ∀ {φ ψ : LTL AP},
        LTLFormulaDPACompilation.{ap, max u v x y, aut} interp φ ->
        LTLFormulaDPACompilation.{ap, max u v x y, aut} interp ψ ->
          LTLFormulaDPACompilation.{ap, max u v x y, aut} interp (LTL.until φ ψ))
    (formula : LTL AP)
    (gameCompiler :
      DPATrackingFiniteGameCompiler.{u, v, x, y, a} In₁ In₂ Out₁ Out₂) :
    EffectiveParitySpecification.{u, v, x, y, a, max u v x y}
      In₁ In₂ Out₁ Out₂ :=
  (LTLDPAUntilMullerBuildingBlocks.ofLAR interp dec untilC)
    |>.toMullerBuildingBlocks.toEffectiveParitySpecificationFromTrackingCompiler
      formula gameCompiler

/--
Until-only LAR LTL route with the paper-facing rotating rational-run compiler.

This is the narrow direct endpoint for the remaining two real constructions:
a certified `until` constructor and a concrete uniform rational-run epoch
compiler.
-/
noncomputable def LTLFormulaDPACompilation.toEffectiveParitySpecificationOfUntilLARRationalRunCompiler
    {AP : Type ap}
    {In₁ : Type u}
    {In₂ : Type v}
    {Out₁ : Type x}
    {Out₂ : Type y}
    [DecidableEq AP]
    [Inhabited In₁]
    [Inhabited In₂]
    [Fintype In₁]
    [Fintype In₂]
    [Fintype Out₁]
    [Fintype Out₂]
    (interp : AP -> RoundRecord In₁ In₂ Graph Out₁ Out₂ -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (untilC :
      LTLUntilDPAConstructor.{ap, max u v x y, aut} interp)
    (formula : LTL AP)
    (gameCompiler :
      DPARotatingRationalRunEpochCompiler.{u, v, x, y, ap, a, b, aut}
        In₁ In₂ Out₁ Out₂) :
    EffectiveParitySpecification.{u, v, x, y, max u v x y, max u v x y}
      In₁ In₂ Out₁ Out₂ :=
  (LTLUntilDPAConstructor.toCompiler interp dec untilC)
    |>.toEffectiveParitySpecificationFromRationalRunCompiler
      formula gameCompiler

/--
Tracking-style variant of the until-only LAR rational-run route.
-/
noncomputable def LTLFormulaDPACompilation.toEffectiveParitySpecificationOfUntilLARRationalRunTrackingCompiler
    {AP : Type ap}
    {In₁ : Type u}
    {In₂ : Type v}
    {Out₁ : Type x}
    {Out₂ : Type y}
    [DecidableEq AP]
    [Inhabited In₁]
    [Inhabited In₂]
    [Fintype In₁]
    [Fintype In₂]
    [Fintype Out₁]
    [Fintype Out₂]
    (interp : AP -> RoundRecord In₁ In₂ Graph Out₁ Out₂ -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (untilC :
      LTLUntilDPAConstructor.{ap, max u v x y, aut} interp)
    (formula : LTL AP)
    (gameCompiler :
      DPARotatingRationalRunEpochCompiler.{u, v, x, y, ap, a, b, aut}
        In₁ In₂ Out₁ Out₂) :
    EffectiveParitySpecification.{u, v, x, y, max u v x y, max u v x y}
      In₁ In₂ Out₁ Out₂ :=
  (LTLUntilDPAConstructor.toCompiler interp dec untilC)
    |>.toEffectiveParitySpecificationFromRationalRunTrackingCompiler
      formula gameCompiler

/--
Arbitrary full-LTL synthesis from the exact remaining reusable automata
constructor and the paper-facing rational-run finite-game compiler.
-/
noncomputable def ltl_until_lar_rational_run_compiler_synthesis_problem_decidable
    {AP : Type ap}
    {In₁ : Type u}
    {In₂ : Type v}
    {Out₁ : Type x}
    {Out₂ : Type y}
    [DecidableEq AP]
    [Inhabited In₁]
    [Inhabited In₂]
    [Fintype In₁]
    [Fintype In₂]
    [Fintype Out₁]
    [Fintype Out₂]
    (interp : AP -> RoundRecord In₁ In₂ Graph Out₁ Out₂ -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (untilC :
      LTLUntilDPAConstructor.{ap, max u v x y, aut} interp)
    (formula : LTL AP)
    (gameCompiler :
      DPARotatingRationalRunEpochCompiler.{u, v, x, y, ap, a, b, aut}
        In₁ In₂ Out₁ Out₂) :
    Decidable
      (SynthesisProblem
        (fun word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂) =>
          LTL.Satisfies interp word formula)) :=
  ltl_dpa_rational_run_compiler_synthesis_problem_decidable
    (LTLUntilDPAConstructor.toCompiler interp dec untilC)
    formula
    gameCompiler

end DistributedSynthesis
