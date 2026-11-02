/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.DecisionTasks.FiniteViews
import DistributedSynthesis.Library.Distributed.DecisionTasks.Source.TaskColouring

/-! # The two-process history encoding and the shared task views

The tree-labelling proof uses compact two-process histories. They carry exactly
the same information as the shared finite-depth views, including the initial
private input and silent rounds. Both representations execute the one protocol
model; the compact history is an internal encoding, not an additional model of
solvability. These statements concern generated views, not malformed constructors.
-/

namespace DistributedSynthesis.DecisionTasks.TwoProcess

variable {V : Type} (σ τ : ℕ → Event Bool) (x y : Bool → V) (r : ℕ) (p : Bool)

/-- Evaluate the history protocol on the shared full-information view. -/
theorem history_of_view :
    FiniteViews.eval (Source.historyAlg V) r (FiniteViews.view σ x r p) =
      Source.hist σ x r p := by
  exact (FiniteViews.eval_view (Source.historyAlg V) σ x r p).trans
    (Source.historyAlg_run σ x r p)

/-- The internal history encoding induces precisely the canonical local observations. -/
theorem history_eq_iff_view_eq :
    Source.hist σ x r p = Source.hist τ y r p ↔
      FiniteViews.view σ x r p = FiniteViews.view τ y r p := by
  constructor
  · intro h
    have hf := Source.fullEq_of_hist_eq h
    have hr := Source.run_eq_of_viewEq
      (FiniteViews.protocol (P := Bool) (I := fun _ => V)) hf.view hf.own hf.2.2
    change FiniteViews.protocol.run σ x r p = FiniteViews.protocol.run τ y r p at hr
    simp only [FiniteViews.protocol_run, Sigma.mk.inj_iff] at hr
    exact eq_of_heq hr.2
  · intro h
    rw [← history_of_view σ x r p, ← history_of_view τ y r p, h]

end DistributedSynthesis.DecisionTasks.TwoProcess
