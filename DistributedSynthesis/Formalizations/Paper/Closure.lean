/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.GraphAdversaries.GeometryTopology

/-!
# The geometric map preserves closure

Manuscript source label: `pi:closure`.

## Paper statement

For any message adversary $A \subseteq \Gamma^\omega$, we have $\pi(\overline{A}) = \overline{\pi(A)}$.

## Reading the proof

See the [proof locations](PROOFS.md#the-geometric-map-preserves-closure) for direct links to the
underlying declarations. The full Lean statements and proofs follow below.
-/

open DistributedSynthesis Characterisation

namespace DistributedSynthesis.Paper.Closure

/-- Reuses `Characterisation.geometricMap_image_closure`. -/
theorem geometricMap_image_closure :
    ∀ [inst : TopologicalSpace Graph] [DiscreteTopology Graph] (A : Set (ℕ → Graph)),
      geometricMap '' closure A = closure (geometricMap '' A) :=
  @_root_.Characterisation.geometricMap_image_closure

end DistributedSynthesis.Paper.Closure
