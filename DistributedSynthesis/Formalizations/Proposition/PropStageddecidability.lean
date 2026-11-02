/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Proposition.PropSaturationbasis

/-!
# Staged route to decidability

This file packages `prop:stageddecidability`: stable synchronized-block bases
plus a finite direct-reversal handoff give a full finite regular-test route,
and hence decidability.
-/

namespace DistributedSynthesis

universe u v

/-- Certificate for the staged decidability route. -/
structure StagedDecidabilityCertificate
    (Automaton : Type u)
    (Realizable : Prop) where
  noDirectReversalSaturationStabilizes : Prop
  finiteDirectReversalHandoff : Prop
  fullRegularTestRoute : RegularTestRouteDecisionCertificate.{u, v} Automaton Realizable
  noDirectReversalSaturationStabilizes_proof : noDirectReversalSaturationStabilizes
  finiteDirectReversalHandoff_proof : finiteDirectReversalHandoff

/--
Named theorem-shaped decision extractor for the staged route.

Use this when a later proposition needs `Nonempty (Decidable Realizable)`
rather than the bare decision procedure.
-/
theorem staged_route_decidable_nonempty
    {Automaton : Type u} {Realizable : Prop}
    (cert : StagedDecidabilityCertificate Automaton Realizable) :
    Nonempty (Decidable Realizable) :=
  saturation_basis_route_to_decidability cert.fullRegularTestRoute

/--
Proposition `prop:stageddecidability`: the staged construction supplies the
regular-test route and therefore decidability.
-/
theorem staged_route_to_decidability
    {Automaton : Type u} {Realizable : Prop}
    (cert : StagedDecidabilityCertificate Automaton Realizable) :
    cert.noDirectReversalSaturationStabilizes ∧
      cert.finiteDirectReversalHandoff ∧
      Nonempty (Decidable Realizable) := by
  exact
    ⟨cert.noDirectReversalSaturationStabilizes_proof,
      cert.finiteDirectReversalHandoff_proof,
      staged_route_decidable_nonempty cert⟩

/--
Named decision extractor for the staged route.
-/
noncomputable def staged_route_decidable
    {Automaton : Type u} {Realizable : Prop}
    (cert : StagedDecidabilityCertificate Automaton Realizable) :
    Decidable Realizable :=
  saturation_basis_route_decidable cert.fullRegularTestRoute

end DistributedSynthesis
