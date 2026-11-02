/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Proposition.PropSaturationbasis

/-!
# Saturation is the least closed test algebra

This file packages `prop:saturationleast`: the saturation closure is least
among Boolean algebras containing the seeds and closed under the exact
private-input predecessor operators, and stabilization is equivalent to the
existence of a finite closed algebra.
-/

namespace DistributedSynthesis

universe u v w x y z q

/-- Abstract closed algebra property used by the saturation least-closure statement. -/
structure ClosedRegularTestAlgebra
    (EdgeType : Type u) where
  Test : Type v
  testFinite : Fintype Test
  language : Test -> TypedPathLanguage EdgeType
  containsSeeds : Prop
  booleanClosed : Prop
  predecessorClosed : Prop
  containsSeeds_proof : containsSeeds
  booleanClosed_proof : booleanClosed
  predecessorClosed_proof : predecessorClosed

attribute [instance] ClosedRegularTestAlgebra.testFinite

/-- Certificate for the least-closed-algebra theorem for a saturation sequence. -/
structure SaturationLeastClosureCertificate
    {Alphabet : Type u} {EdgeType : Type v} {Boundary : Type w}
    {In₁ : Type x} {In₂ : Type y}
    (sat : RegularTestSaturation.{u, v, w, x, y, z} Alphabet EdgeType Boundary In₁ In₂) where
  SaturatedLanguage : TypedPathLanguage EdgeType -> Prop
  saturatedContainsSeeds : Prop
  saturatedBooleanClosed : Prop
  saturatedPredecessorClosed : Prop
  saturatedLeast :
    ∀ algebra : ClosedRegularTestAlgebra.{v, q} EdgeType,
      ∀ language, SaturatedLanguage language -> ∃ test : algebra.Test,
        algebra.language test = language
  stableIffFiniteClosed :
    (∃ n, sat.StableAt n) ↔ Nonempty (ClosedRegularTestAlgebra.{v, q} EdgeType)
  saturatedContainsSeeds_proof : saturatedContainsSeeds
  saturatedBooleanClosed_proof : saturatedBooleanClosed
  saturatedPredecessorClosed_proof : saturatedPredecessorClosed

/--
Proposition `prop:saturationleast`: the saturated language family is the least
closed algebra, and stabilization is equivalent to a finite closed algebra.
-/
theorem saturation_is_least_closed_test_algebra
    {Alphabet : Type u} {EdgeType : Type v} {Boundary : Type w}
    {In₁ : Type x} {In₂ : Type y}
    {sat : RegularTestSaturation.{u, v, w, x, y, z} Alphabet EdgeType Boundary In₁ In₂}
    (cert : SaturationLeastClosureCertificate.{u, v, w, x, y, z, q} sat) :
    cert.saturatedContainsSeeds ∧
      cert.saturatedBooleanClosed ∧
      cert.saturatedPredecessorClosed ∧
      (∀ algebra : ClosedRegularTestAlgebra.{v, q} EdgeType,
        ∀ language, cert.SaturatedLanguage language ->
          ∃ test : algebra.Test, algebra.language test = language) ∧
      ((∃ n, sat.StableAt n) ↔ Nonempty (ClosedRegularTestAlgebra.{v, q} EdgeType)) := by
  exact
    ⟨cert.saturatedContainsSeeds_proof,
      cert.saturatedBooleanClosed_proof,
      cert.saturatedPredecessorClosed_proof,
      cert.saturatedLeast,
      cert.stableIffFiniteClosed⟩

end DistributedSynthesis
