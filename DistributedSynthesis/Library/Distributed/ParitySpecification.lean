/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.Execution
import DistributedSynthesis.Formalizations.Theorem.ThmDynhiersynth

/-! # Finite parity-game certificates for synthesis

This is the conditional certificate API, separated from execution
semantics. Its certificate premise and noncomputable decision declaration are
unchanged; this module does not supply an encoded computable compiler.
-/

namespace DistributedSynthesis

universe u v x y a b

/--
A specification with an effective finite parity-game compilation.

This is the formal target used by `thm:main`: the Lean development proves
decidability for specifications supplied together with a finite game and a proof
that finite-game realizability is equivalent to realizability of the original
execution predicate.  LTL specifications enter this target once the automata
backend has produced the finite-game certificate recorded below.  The separate
LTL files define full LTL syntax and prove the semantic front end to the
certificate boundary; the constructive APA-to-DPA determinization and the
paper-specific finite-game compilation are not hidden in this structure.
-/
structure EffectiveParitySpecification
    (In₁ : Type u) (In₂ : Type v) (Out₁ : Type x) (Out₂ : Type y) where
  predicate : Specification In₁ In₂ Out₁ Out₂
  finiteGame : FiniteDynamicHierarchyParityGame.{a, b}
  realizabilityEquivalent :
    finiteGame.realizable ↔
      ∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂, predicate (execution σ env)

/--
Alias emphasizing the precise formal scope: an LTL/parity specification is in
scope for the verified theorem once it has been effectively compiled to the
finite parity-game certificate above.
-/
abbrev EffectivelyCompiledParitySpecification
    (In₁ : Type u) (In₂ : Type v) (Out₁ : Type x) (Out₂ : Type y) :=
  EffectiveParitySpecification.{u, v, x, y, a, b} In₁ In₂ Out₁ Out₂

/-- Synthesis problem for effectively compiled parity specifications. -/
def EffectiveParitySynthesisProblem
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (φ : EffectiveParitySpecification In₁ In₂ Out₁ Out₂) : Prop :=
  SynthesisProblem φ.predicate

/-- Effective parity specifications are decidable once their finite game is built. -/
noncomputable def effective_parity_synthesis_problem_decidable
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (φ : EffectiveParitySpecification.{u, v, x, y, a, b} In₁ In₂ Out₁ Out₂) :
    Decidable (EffectiveParitySynthesisProblem φ) := by
  let finiteGameDecision := finite_dynamic_hierarchy_parity_game_decidable φ.finiteGame
  cases finiteGameDecision with
  | isTrue h =>
      exact isTrue (φ.realizabilityEquivalent.mp h)
  | isFalse h =>
      exact isFalse (fun hSynth => h (φ.realizabilityEquivalent.mpr hSynth))

end DistributedSynthesis
