/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.DecisionTasks.IISFiniteViews

/-! # Executable search at a fixed IIS depth

Both the graph prefixes and the local decision tables are finite. `check`
exhaustively checks one depth; the proved equivalence says that some depth
succeeds exactly when the arbitrary-state task is solvable. It does not
supply a computable bound on the depth of a possible solver.
-/

namespace DistributedSynthesis.DecisionTasks.IISFiniteSearch

open FiniteViews

abbrev Letter := {g : IISGraphs.Graph // g ∈ IISGraphs.graphs}

def defaultLetter : Letter := ⟨IISGraphs.rankGraph (fun _ => 0), by decide⟩

variable {I O : Fin 3 → Type}

/-- Compute the view from a finite word of admissible graph letters. -/
def prefixView (x : ∀ p, I p) : (k : ℕ) → (Fin k → Letter) → Fin 3 → View (Fin 3) I k
  | 0, _, p => ⟨p, x p⟩
  | k + 1, w, p => (p, prefixView x k (fun j => w j.castSucc) p,
      fun q => if q ∈ (IISGraphs.event (w (Fin.last k)).val).inN p then
        some (prefixView x k (fun j => w j.castSucc) q) else none)

theorem prefixView_correct (x : ∀ p, I p) (k : ℕ) (w : Fin k → Letter)
    (σ : ℕ → Source.Event (Fin 3))
    (hσ : ∀ j : Fin k, σ j = IISGraphs.event (w j).val) (p : Fin 3) :
    prefixView x k w p = view σ x k p := by
  induction k generalizing p with
  | zero => rfl
  | succ k ih =>
    have hpref (j : Fin k) : σ j = IISGraphs.event (w j.castSucc).val := hσ j.castSucc
    have hlast : σ k = IISGraphs.event (w (Fin.last k)).val := hσ (Fin.last k)
    simp only [prefixView, view, ih _ hpref, hlast]

/-- Extend a finite graph prefix by the complete graph. -/
def extend {k : ℕ} (w : Fin k → Letter) (r : ℕ) : Letter :=
  if h : r < k then w ⟨r, h⟩ else defaultLetter

theorem view_maps_iff_prefix_maps (k : ℕ) (d : ∀ p, View (Fin 3) I k → O p)
    (T : DecisionTasks.Task (Fin 3) I O) :
    (∀ σ ∈ Source.advIIS (Fin 3), ∀ x, T.allows x (fun p => d p (view σ x k p))) ↔
      ∀ (w : Fin k → Letter) x, T.allows x (fun p => d p (prefixView x k w p)) := by
  constructor
  · intro h w x
    let σ := fun r => IISGraphs.event (extend w r).val
    have hs : σ ∈ Source.advIIS (Fin 3) :=
      fun r => (IISGraphs.mem_graphs_iff _).mp (extend w r).property
    have heq (p : Fin 3) : prefixView x k w p = view σ x k p :=
      prefixView_correct x k w σ (fun j => by simp [σ, extend, j.isLt]) p
    simpa only [heq] using h σ hs x
  · intro h σ hσ x
    let w : Fin k → Letter := fun j => ⟨IISGraphs.encode (σ j),
      (IISGraphs.mem_graphs_iff _).mpr (by rw [IISGraphs.event_encode]; exact hσ j)⟩
    have heq (p : Fin 3) : prefixView x k w p = view σ x k p :=
      prefixView_correct x k w σ (fun j => (IISGraphs.event_encode (σ j)).symm) p
    simpa only [heq] using h w x

def HasMapAt (T : DecisionTasks.Task (Fin 3) I O) (k : ℕ) : Prop :=
  ∃ d : ∀ p, View (Fin 3) I k → O p,
    ∀ (w : Fin k → Letter) x, T.allows x (fun p => d p (prefixView x k w p))

instance [∀ p, Fintype (I p)] [∀ p, DecidableEq (I p)]
    [∀ p, Fintype (O p)] (T : DecisionTasks.Task (Fin 3) I O)
    [∀ x o, Decidable (T.allows x o)] (k : ℕ) : Decidable (HasMapAt T k) := by
  unfold HasMapAt
  infer_instance

/-- Finite exhaustive search; no classical decision oracle occurs in this definition. -/
def check [∀ p, Fintype (I p)] [∀ p, DecidableEq (I p)]
    [∀ p, Fintype (O p)] (T : DecisionTasks.Task (Fin 3) I O)
    [∀ x o, Decidable (T.allows x o)] (k : ℕ) : Bool := decide (HasMapAt T k)

theorem solvable_iff_exists_map [∀ p, Finite (I p)] [∀ p, Nonempty (O p)]
    (T : DecisionTasks.Task (Fin 3) I O) :
    T.Solvable (Source.advIIS (Fin 3)) ↔ ∃ k, HasMapAt T k := by
  rw [FiniteViews.iis_solvable_iff_view_maps]
  apply exists_congr
  intro k
  apply exists_congr
  intro d
  exact view_maps_iff_prefix_maps k d T

theorem check_correct [∀ p, Fintype (I p)] [∀ p, DecidableEq (I p)]
    [∀ p, Fintype (O p)] [∀ p, Nonempty (O p)]
    (T : DecisionTasks.Task (Fin 3) I O) [∀ x o, Decidable (T.allows x o)] :
    T.Solvable (Source.advIIS (Fin 3)) ↔ ∃ k, check T k = true := by
  simp only [check, decide_eq_true_eq, ← solvable_iff_exists_map T]

end DistributedSynthesis.DecisionTasks.IISFiniteSearch
