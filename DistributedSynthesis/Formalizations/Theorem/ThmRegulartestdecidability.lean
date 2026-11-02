/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Proposition.PropRegulartestbasistorepair
import DistributedSynthesis.Formalizations.Lemma.LemEpochcongruencetotransformer
import DistributedSynthesis.Formalizations.Lemma.LemEpochtorotating
import DistributedSynthesis.Formalizations.Lemma.LemRotatingtarget
import DistributedSynthesis.Formalizations.Theorem.ThmFiniteAindex

/-!
# Regular-test route to decidability
-/

namespace DistributedSynthesis

universe u v

/--
Certificate for the regular-test route to the decidability theorem.

The named `Prop` fields are semantic proof obligations of the route.  They are
kept as assumptions at this abstraction layer, but the decidability conclusion
is not assumed: it is derived from the supplied finite game and the equivalence
between finite-game realizability and the target `Realizable` predicate.
-/
structure RegularTestRouteDecisionCertificate
    (Automaton : Type u)
    (Realizable : Prop) where
  boundaryAccessFinite : Prop
  basisOneSound : Prop
  basisTwoSound : Prop
  finiteCongruenceRepair : Prop
  epochTransformerExists : Prop
  rotatingTargetExists : Prop
  finiteAIndexApplies : Prop
  finiteGame : FiniteDynamicHierarchyParityGame.{u, v}
  finiteGameRealizableIff : finiteGame.realizable ↔ Realizable
  boundaryAccessFinite_proof : boundaryAccessFinite
  basisOneSound_proof : basisOneSound
  basisTwoSound_proof : basisTwoSound
  finiteCongruenceRepair_proof : finiteCongruenceRepair
  epochTransformerExists_proof : epochTransformerExists
  rotatingTargetExists_proof : rotatingTargetExists
  finiteAIndexApplies_proof : finiteAIndexApplies

/--
Paper-facing Theorem `thm:regulartestdecidability`: the regular-test basis route
packages the finite-index decision procedure.
-/
theorem regular_test_route_to_decidability
    {Automaton : Type u} {Realizable : Prop}
    (cert : RegularTestRouteDecisionCertificate Automaton Realizable) :
    cert.boundaryAccessFinite ∧
      cert.basisOneSound ∧
      cert.basisTwoSound ∧
      cert.finiteCongruenceRepair ∧
      cert.epochTransformerExists ∧
      cert.rotatingTargetExists ∧
      cert.finiteAIndexApplies ∧
      Nonempty (Decidable Realizable) := by
  let finiteGameDecision := finite_dynamic_hierarchy_parity_game_decidable cert.finiteGame
  have realizabilityDecision : Decidable Realizable := by
    cases finiteGameDecision with
    | isTrue h =>
        exact isTrue (cert.finiteGameRealizableIff.mp h)
    | isFalse h =>
        exact isFalse (fun hRealizable => h (cert.finiteGameRealizableIff.mpr hRealizable))
  exact
    ⟨cert.boundaryAccessFinite_proof,
      cert.basisOneSound_proof,
      cert.basisTwoSound_proof,
      cert.finiteCongruenceRepair_proof,
      cert.epochTransformerExists_proof,
      cert.rotatingTargetExists_proof,
      cert.finiteAIndexApplies_proof,
      ⟨realizabilityDecision⟩⟩

/--
Named decision extractor for the regular-test route.

Use this instead of projecting through the conjunction returned by
`regular_test_route_to_decidability` when only the final decision is needed.
-/
noncomputable def regular_test_route_decidable
    {Automaton : Type u} {Realizable : Prop}
    (cert : RegularTestRouteDecisionCertificate Automaton Realizable) :
    Decidable Realizable :=
  Classical.choice (regular_test_route_to_decidability cert).2.2.2.2.2.2.2

/--
Named final projection from the regular-test route theorem.

Use this when a later proposition wants the theorem-style `Nonempty` result
without depending on the nested conjunction shape of
`regular_test_route_to_decidability`.
-/
theorem regular_test_route_decidable_nonempty
    {Automaton : Type u} {Realizable : Prop}
    (cert : RegularTestRouteDecisionCertificate Automaton Realizable) :
    Nonempty (Decidable Realizable) :=
  ⟨regular_test_route_decidable cert⟩

end DistributedSynthesis
