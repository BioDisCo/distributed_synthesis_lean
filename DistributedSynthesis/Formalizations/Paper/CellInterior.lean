/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.GraphAdversaries.GeometryTopology

/-!
# The preimage of an interval interior

Manuscript source label: `pi:inverse:J:interior`.

## Paper statement

For every finite graph history $h\in\Gamma^*$, we have $\pi^{-1}(J(h)^\circ) \subseteq h\cdot\Gamma^\omega$.

## Reading the proof

See the [proof locations](PROOFS.md#the-preimage-of-an-interval-interior) for direct links to the
underlying declarations. The full Lean statements and proofs follow below.
-/

open DistributedSynthesis Characterisation

namespace DistributedSynthesis.Paper.CellInterior

/-- Reuses `Characterisation.relative_interior_cell_forces_prefix`. -/
theorem relative_interior_cell_forces_prefix :
    ∀ (word : ℕ → Graph) (h : List Graph),
      geometricMap word ∈ interior {x : ↑UnitInterval | ↑x ∈ Set.Icc (leftEndpoint h) (rightEndpoint h)} →
        graphPrefix word h.length = h :=
  @_root_.Characterisation.relative_interior_cell_forces_prefix

end DistributedSynthesis.Paper.CellInterior
