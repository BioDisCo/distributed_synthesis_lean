/- Project authors: see AUTHORS.md at the repository root. -/
import DistributedSynthesis.Library.Distributed.GraphExecutions

namespace DistributedSynthesis.FullViewPath
open ScalingRow

/-- Agreement on each edge forces one label on the entire inputless row.
Only the indicated round is constrained; labels and algorithms are arbitrary. -/
theorem edge_agreement_implies_uniform {O : Type*}
    (σ : StrategyPair Unit Unit O O) (r : Nat)
    (agree : ∀ h : List Graph, h.length = r → σ.one (evaluate h).one = σ.two (evaluate h).two) :
    ∃ value : O, ∀ h : List Graph, h.length = r →
      σ.one (evaluate h).one = value ∧ σ.two (evaluate h).two = value := by
  let label : Vertex → O := Sum.elim σ.one σ.two
  let first := blind^[r] (left root)
  have edges (s : Cell) (member : s ∈ row r) : label (left s) = label (right s) := by
    obtain ⟨h, len, rfl⟩ := (mem_row_iff r s).mp member
    have same := agree h len
    cases orientation : (evaluate h).oneLeft <;>
      simp [label, left, right, orientation, same]
  have uniform (v : Vertex) (visited : Path.Visits right first (row r) v) :
      label v = label first :=
    (row_path r).fiber_uniform (fun _ => 0) label
      (fun _ _ => Nat.le_refl 0) (fun s member _ => edges s member)
      visited (Or.inl rfl) rfl
  refine ⟨label first, fun h len => ?_⟩
  have visited := endpoints_visited ((mem_row_iff r (evaluate h)).mpr ⟨h, len, rfl⟩)
  have lo := uniform _ visited.1
  have hi := uniform _ visited.2
  cases orientation : (evaluate h).oneLeft <;>
    simp only [left, right, orientation, Bool.false_eq_true, ↓reduceIte, label, Sum.elim_inl,
      Sum.elim_inr] at lo hi <;> exact ⟨by assumption, by assumption⟩

/-- `lem:agreement_on_path`, with its execution hypothesis. Round `n+1`
in the manuscript is execution index `n`; every finite edge is extended
using the existing graph-execution adapter. -/
theorem execution_agreement_implies_uniform {O : Type*}
    (σ : StrategyPair Unit Unit O O) (n : Nat)
    (agree : ∀ env : EnvironmentSequence Unit Unit,
      (execution σ env n).outputOne = (execution σ env n).outputTwo) :
    ∃ value : O, ∀ h : List Graph, h.length = n+1 →
      σ.one (evaluate h).one = value ∧ σ.two (evaluate h).two = value := by
  apply edge_agreement_implies_uniform
  intro h len
  have outputs := GraphExecutions.extend_outputs σ h (by omega)
  rw [len, Nat.add_sub_cancel] at outputs
  exact outputs.1.symm.trans ((agree (GraphExecutions.extend h)).trans outputs.2)

/-- The same argument for a selected part of an output label, such as its
control state and zero flag. No conditions on the other fields are needed. -/
theorem projected_execution_agreement_implies_uniform {O L : Type*}
    (σ : StrategyPair Unit Unit O O) (project : O → L) (n : Nat)
    (agree : ∀ env : EnvironmentSequence Unit Unit,
      project (execution σ env n).outputOne = project (execution σ env n).outputTwo) :
    ∃ value : L, ∀ h : List Graph, h.length = n+1 →
      project (σ.one (evaluate h).one) = value ∧ project (σ.two (evaluate h).two) = value := by
  let projected : StrategyPair Unit Unit L L :=
    ⟨fun v => project (σ.one v), fun v => project (σ.two v)⟩
  apply edge_agreement_implies_uniform projected
  intro h len
  have outputs := GraphExecutions.extend_outputs σ h (by omega)
  rw [len, Nat.add_sub_cancel] at outputs
  exact (congrArg project outputs.1).symm.trans
    ((agree (GraphExecutions.extend h)).trans (congrArg project outputs.2))

end DistributedSynthesis.FullViewPath
