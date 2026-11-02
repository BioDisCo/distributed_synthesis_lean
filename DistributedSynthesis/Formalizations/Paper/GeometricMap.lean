/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.GraphAdversaries.GeometryTopology

/-!
# Continuity and surjectivity of the geometric map

Manuscript source label: `pi:cont`.

## Paper statement

The map $\pi\colon \Gamma^\omega \to [0,1]$ is continuous and surjective.

## Reading the proof

See the [proof locations](PROOFS.md#continuity-and-surjectivity-of-the-geometric-map) for direct links to the
underlying declarations. The full Lean statements and proofs follow below.
-/

open DistributedSynthesis Characterisation

namespace DistributedSynthesis.Paper.GeometricMap

/-- Reuses `Characterisation.continuous_geometricMap`. -/
theorem continuous_geometricMap :
    ∀ [inst : TopologicalSpace Graph] [DiscreteTopology Graph], Continuous geometricMap :=
  @_root_.Characterisation.continuous_geometricMap

/-- Reuses `Characterisation.geometricMap_surjective`. -/
theorem geometricMap_surjective :
    Function.Surjective geometricMap :=
  @_root_.Characterisation.geometricMap_surjective

/-- Reuses `Characterisation.coordinate_unique`. -/
theorem coordinate_unique :
    ∀ (word : ℕ → Graph) (x : ℝ),
      (∀ (n : ℕ), x ∈ Set.Icc (leftEndpoint (graphPrefix word n)) (rightEndpoint (graphPrefix word n))) →
        coordinate word = x :=
  @_root_.Characterisation.coordinate_unique

end DistributedSynthesis.Paper.GeometricMap
