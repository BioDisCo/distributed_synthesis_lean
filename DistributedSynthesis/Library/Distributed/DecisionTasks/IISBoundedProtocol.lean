/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.DecisionTasks.BoundedProtocol
import DistributedSynthesis.Library.Distributed.DecisionTasks.IISGraphs

/-! # Uniformly bounded protocols for IIS

The compact termination theorem supplies the finite round used by the
generic bounded-protocol characterization.
-/

namespace DistributedSynthesis.DecisionTasks

/-- Finite inputs suffice; the original protocol may have arbitrary states. -/
theorem IISGraphs.solvable_iff_bounded {I O : Fin 3 → Type}
    [∀ p, Finite (I p)] [∀ p, Nonempty (O p)] (T : Task (Fin 3) I O) :
    T.Solvable (Source.advIIS (Fin 3)) ↔ T.BoundedSolvable (Source.advIIS (Fin 3)) := by
  classical
  constructor
  · rintro ⟨St, A, out, h⟩
    obtain ⟨k, hk⟩ := IISGraphs.uniform_bound A out T h
    let fallback : ∀ p, O p := fun p => Classical.choice inferInstance
    refine ⟨k, St, A, fun p s => (out p s).getD (fallback p), ?_⟩
    intro σ hσ x
    apply h.allows σ hσ x
    intro p
    obtain ⟨o, ho⟩ := hk σ hσ x p
    exact ⟨k, by simp only [ho, Option.getD_some]⟩
  · exact Task.BoundedSolvable.solvable


end DistributedSynthesis.DecisionTasks
