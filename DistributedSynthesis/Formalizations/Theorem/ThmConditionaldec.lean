/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFringeelim
import DistributedSynthesis.Formalizations.Theorem.ThmDynhiersynth

/-!
# Conditional decidability via finite fringe

This file packages `thm:conditionaldec`: if the acknowledgement-only
incomparability can be compiled into a uniformly finite fringe while preserving
realizability, then the resulting finite dynamic-hierarchy parity game gives a
decision procedure.
-/

namespace DistributedSynthesis

universe u v

/--
Certificate for the conditional finite-fringe route.  The field
`realizabilityEquivalent` is the formal version of "without changing
realizability"; `finiteGame` is the compiled finite game to which
`thm:dynhiersynth` applies.
-/
structure ConditionalFiniteFringeCompilationCertificate
    (Realizable : Prop) where
  finiteGame : FiniteDynamicHierarchyParityGame.{u, v}
  finiteFringeCompilation : Prop
  realizabilityEquivalent : finiteGame.realizable ↔ Realizable
  finiteFringeCompilation_proof : finiteFringeCompilation

/--
Theorem `thm:conditionaldec`: a realizability-preserving finite-fringe
compilation into a finite dynamic-hierarchy parity game yields decidability.
-/
noncomputable def conditional_decidability_from_finite_fringe
    {Realizable : Prop}
    (cert : ConditionalFiniteFringeCompilationCertificate.{u, v} Realizable) :
    Decidable Realizable := by
  let finiteDecision := finite_dynamic_hierarchy_parity_game_decidable cert.finiteGame
  cases finiteDecision with
  | isTrue h =>
      exact isTrue (cert.realizabilityEquivalent.mp h)
  | isFalse h =>
      exact isFalse (fun hRealizable =>
        h (cert.realizabilityEquivalent.mpr hRealizable))

/-- Paper-facing package exposing the finite-fringe and hierarchy side conditions. -/
theorem conditional_decidability_certificate
    {Realizable : Prop}
    (cert : ConditionalFiniteFringeCompilationCertificate.{u, v} Realizable) :
    cert.finiteFringeCompilation ∧
      cert.finiteGame.dynamicHierarchy ∧
      cert.finiteGame.parityObjective ∧
      Nonempty (Decidable Realizable) := by
  exact
    ⟨cert.finiteFringeCompilation_proof,
      cert.finiteGame.dynamicHierarchy_proof,
      cert.finiteGame.parityObjective_proof,
      ⟨conditional_decidability_from_finite_fringe cert⟩⟩

end DistributedSynthesis
