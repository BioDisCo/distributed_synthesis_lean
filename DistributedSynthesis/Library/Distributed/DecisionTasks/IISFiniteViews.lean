/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.DecisionTasks.FiniteViews
import DistributedSynthesis.Library.Distributed.DecisionTasks.IISParticipation

/-! # IIS and participation criteria over the shared finite local views -/

namespace DistributedSynthesis.DecisionTasks.FiniteViews

variable {P : Type} {I O : P → Type}

/-- The full three-process IIS solvability criterion has genuinely finite tables. -/
theorem iis_solvable_iff_view_maps {I O : Fin 3 → Type}
    [∀ p, Finite (I p)] [∀ p, Nonempty (O p)] (T : DecisionTasks.Task (Fin 3) I O) :
    T.Solvable (Source.advIIS (Fin 3)) ↔
      ∃ (k : ℕ) (d : ∀ p, View (Fin 3) I k → O p),
        ∀ σ ∈ Source.advIIS (Fin 3), ∀ x,
          T.allows x (fun p => d p (view σ x k p)) :=
  (IISGraphs.solvable_iff_bounded T).trans (bounded_iff_view_maps T _)

/-- The partial-participation criterion uses one finite local table at each depth. -/
theorem participation_iff_view_maps (T : IISParticipation.Task P I O) :
    T.BoundedSolvable ↔
      ∃ (k : ℕ) (d : ∀ p, View P (fun p => Option (I p)) k → Option (O p)),
        ∀ σ ∈ Source.advIIS P, ∀ x, T.legal x →
          let o : IISParticipation.Assignment P O := fun p =>
            if IISParticipation.active x p then
              d p (view (fun n => IISParticipation.restrict (IISParticipation.active x) (σ n))
                x k p) else none
          IISParticipation.sameSupport x o ∧ T.allows x o := by
  classical
  constructor
  · rintro ⟨k, St, A, out, h⟩
    refine ⟨k, fun p v => out p (eval A k v), ?_⟩
    simpa only [eval_view] using h
  · rintro ⟨k, d, h⟩
    let decision : ∀ p, State P (fun p => Option (I p)) → Option (O p) := fun p s =>
      if hr : s.1 = k then d p (hr ▸ s.2) else none
    refine ⟨k, State P (fun p => Option (I p)), protocol, decision, ?_⟩
    intro σ hσ x hx
    change IISParticipation.sameSupport x (fun p =>
      if IISParticipation.active x p then decision p
        (protocol.run (fun n => IISParticipation.restrict (IISParticipation.active x) (σ n))
          x k p) else none) ∧ T.allows x (fun p =>
      if IISParticipation.active x p then decision p
        (protocol.run (fun n => IISParticipation.restrict (IISParticipation.active x) (σ n))
          x k p) else none)
    simpa only [protocol_run, decision, dite_true] using h σ hσ x hx


end DistributedSynthesis.DecisionTasks.FiniteViews
