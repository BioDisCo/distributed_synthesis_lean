/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.GraphAdversaries.GeometryTopology

/-!
# Prefix cylinders are clopen

Manuscript source label: `cones:are:clopen`.

## Paper statement

For every finite graph history~$h\in\Gamma^*$, the set~$h\cdot\Gamma^\omega$ of infinite graph histories extending~$h$ is clopen.

## Reading the proof

See the [proof locations](PROOFS.md#prefix-cylinders-are-clopen) for direct links to the
underlying declarations. The full Lean statements and proofs follow below.
-/

open DistributedSynthesis Characterisation

namespace DistributedSynthesis.Paper.ClopenCones

/-- Reuses `Characterisation.isClopen_graphPrefix`. -/
theorem isClopen_graphPrefix :
    ∀ [inst : TopologicalSpace Graph] [DiscreteTopology Graph] (h : List Graph),
      IsClopen {word : ℕ → Graph | graphPrefix word h.length = h} :=
  @_root_.Characterisation.isClopen_graphPrefix

end DistributedSynthesis.Paper.ClopenCones
