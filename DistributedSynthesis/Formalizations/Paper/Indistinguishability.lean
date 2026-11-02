/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.ViewIndistinguishability

/-!
# Indistinguishability and preceding views

Manuscript source label: `lem:IndistDownClosed`.

## Paper statement

Suppose that $h = h_0\cdot (x_1, x_2, g)$ and $h' = h_0' \cdot (x_1', x_2', g')$.
   If $h \sim_p h'$ then $h_0 \sim_p h_0'$, and moreover $p$ has an incoming arrow in both $g$ and $g'$ or it does not have an incoming arrow in either graph.

## Reading the proof

See the [proof locations](PROOFS.md#indistinguishability-and-preceding-views-and-preceding-views-and-preceding-views) for direct links to the
underlying declarations. The full Lean statements and proofs follow below.
-/

open DistributedSynthesis

namespace DistributedSynthesis.Paper.Indistinguishability

universe u_1 u_2 u_3 u_4

/-- Reuses `DistributedSynthesis.indistinguishable_append`. -/
theorem indistinguishable_append :
    ∀ {I₁ : Type u_1} {I₂ : Type u_2} {O₁ : Type u_3} {O₂ : Type u_4} (p : Proc)
      (h k : History I₁ I₂ Graph O₁ O₂) (r s : RoundRecord I₁ I₂ Graph O₁ O₂)
      (same : currentView p (h.append r) = currentView p (k.append s)),
      currentView p h = currentView p k ∧
        ((match p with
          | Proc.one => r.graph ≠ Graph.right
          | Proc.two => r.graph ≠ Graph.left) ↔
          match p with
          | Proc.one => s.graph ≠ Graph.right
          | Proc.two => s.graph ≠ Graph.left) :=
  @_root_.DistributedSynthesis.indistinguishable_append

end DistributedSynthesis.Paper.Indistinguishability
