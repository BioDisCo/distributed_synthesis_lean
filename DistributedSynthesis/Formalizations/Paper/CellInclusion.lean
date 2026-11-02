/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.GraphAdversaries.GeometryTopology

/-!
# Prefixes and inclusion of intervals

Manuscript source label: `J:inclusion:iff:prefix`.

## Paper statement

Let $h, k \in \Gamma^*$ be finite graph histories.
    Then~$h$ is a prefix of~$k$ if and only if $J(k) \subseteq J(h)$.

## Reading the proof

See the [proof locations](PROOFS.md#prefixes-and-inclusion-of-intervals) for direct links to the
underlying declarations. The full Lean statements and proofs follow below.
-/

open DistributedSynthesis Characterisation

namespace DistributedSynthesis.Paper.CellInclusion

/-- Reuses `Characterisation.cell_subset_iff_prefix`. -/
theorem cell_subset_iff_prefix :
    ∀ (h k : List Graph),
      Set.Icc (leftEndpoint k) (rightEndpoint k) ⊆ Set.Icc (leftEndpoint h) (rightEndpoint h) ↔ h <+: k :=
  @_root_.Characterisation.cell_subset_iff_prefix

end DistributedSynthesis.Paper.CellInclusion
