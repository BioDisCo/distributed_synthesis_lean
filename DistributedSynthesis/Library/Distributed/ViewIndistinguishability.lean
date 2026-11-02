/- Project authors: see AUTHORS.md at the repository root. -/
import DistributedSynthesis.Library.Distributed.Views

namespace DistributedSynthesis

/-- `lem:IndistDownClosed`: equal current views imply equal previous views
and the same reception status in the last round. The graph predicate is
written directly, so this basic view fact needs no leader-selection machinery. -/
theorem indistinguishable_append {I₁ I₂ O₁ O₂ : Type*}
    (p : Proc) (h k : History I₁ I₂ Graph O₁ O₂)
    (r s : RoundRecord I₁ I₂ Graph O₁ O₂)
    (same : currentView p (History.append h r) = currentView p (History.append k s)) :
    currentView p h = currentView p k ∧
      ((match p with | .one => r.graph ≠ .right | .two => r.graph ≠ .left) ↔
       (match p with | .one => s.graph ≠ .right | .two => s.graph ≠ .left)) := by
  cases p <;> cases rg : r.graph <;> cases sg : s.graph <;>
    simp [currentView_one_append, currentView_two_append, rg, sg] at same ⊢ <;>
    exact same.1

end DistributedSynthesis
