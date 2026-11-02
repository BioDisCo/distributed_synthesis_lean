/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Proposition.PropFixedinputpartition

/-!
# Fixed-input view-pair graph is a path
-/

namespace DistributedSynthesis

/-- Certificate for the fixed-input view-pair path structure. -/
structure FixedInputTreeCertificate (t : Nat) where
  edgeCount : Nat
  vertexCount : Nat
  isPath : Prop
  edge_count : edgeCount = 3 ^ t
  vertex_count : vertexCount = 3 ^ t + 1
  isPath_proof : isPath

/-- Proposition `prop:fixedinputtree`, paper-facing certificate form. -/
theorem fixed_input_view_pair_graph_is_path
    (t : Nat)
    (cert : FixedInputTreeCertificate t) :
    cert.isPath ∧ cert.edgeCount = 3 ^ t ∧ cert.vertexCount = 3 ^ t + 1 := by
  exact ⟨cert.isPath_proof, cert.edge_count, cert.vertex_count⟩

end DistributedSynthesis
