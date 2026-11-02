/- Project authors: see AUTHORS.md at the repository root. -/
import DistributedSynthesis.Formalizations.Undecidability.RowConditions

namespace DistributedSynthesis.CounterMachine.Paper
open ResidueLTL FullViewPath
variable {Q : Type*}

/-- C0--C5 on the actual labelled inputless view rows. Histories index edges;
the existing left/right functions select their geometric endpoints. There
is no condition on the unused right plan of the final vertex. -/
structure GlobalRows (M : Machine Q)
    (σ : StrategyPair Unit Unit (Output Q) (Output Q)) : Prop where
  position : ∀ h : List Graph, 0 < h.length →
    (σ.one (evaluate h).one).residue = ScalingSafety.ResidueLTL.mod3 (ScalingSafety.coordinate (evaluate h).one) ∧
    (σ.two (evaluate h).two).residue = ScalingSafety.ResidueLTL.mod3 (ScalingSafety.coordinate (evaluate h).two)
  uniform : ∀ n, ∃ q : Q, ∃ z : Fin 2 → Bool, ∀ h : List Graph, h.length = n+1 →
    (σ.one (evaluate h).one).base.control = q ∧ (σ.two (evaluate h).two).base.control = q ∧
    (σ.one (evaluate h).one).base.zero = z ∧ (σ.two (evaluate h).two).base.zero = z
  balance : ∀ h : List Graph, 0 < h.length → ∀ k,
    let l := Rows.emit (projectStrategy σ) (FullViewPath.left (evaluate h))
    let r := Rows.emit (projectStrategy σ) (FullViewPath.right (evaluate h))
    (l.right k).promised + (l.carry k).val =
      (M.op l.control l.zero k).factor * (l.right k).weight.val + (r.carry k).val
  zero : ∀ n k,
    let first := (σ.one (evaluate (List.replicate (n+1) .right)).one).base
    let last := (σ.two (evaluate (List.replicate (n+1) .left)).two).base
    (first.carry k).val = 0 ∧ (last.carry k).val = 0 ∧
    (first.zero k = true → ∀ h : List Graph, h.length = n+1 →
      ((Rows.emit (projectStrategy σ) (FullViewPath.left (evaluate h))).right k).weight.val = 1) ∧
    (first.zero k = false → (first.right k).weight.val = 0)
  initial : ∀ h : List Graph, h.length = 1 →
    (σ.one (evaluate h).one).base.control = M.initial ∧
    (σ.two (evaluate h).two).base.control = M.initial ∧
    ∀ k, ((Rows.emit (projectStrategy σ) (FullViewPath.left (evaluate h))).right k).weight.val = 1
  control : ∀ n,
    (σ.one (evaluate (List.replicate (n+2) .right)).one).base.control =
      M.next (σ.one (evaluate (List.replicate (n+1) .right)).one).base.control
        (σ.one (evaluate (List.replicate (n+1) .right)).one).base.zero
  children : ∀ h : List Graph, 0 < h.length → ∀ g k,
    ((Rows.emit (projectStrategy σ) (FullViewPath.left (evaluate (h++[g])))).right k).weight =
      ((Rows.emit (projectStrategy σ) (FullViewPath.left (evaluate h))).right k).child
        (ScalingSafety.digit (evaluate h).oneLeft g)

/-- No halting state at any actual vertex of a positive-depth row. -/
def NoHaltingOutputs (M : Machine Q) (σ : StrategyPair Unit Unit (Output Q) (Output Q)) : Prop :=
  ∀ h : List Graph, 0 < h.length →
    M.code (σ.one (evaluate h).one).base.control ≠ none ∧
    M.code (σ.two (evaluate h).two).base.control ≠ none

private theorem viewResidues_row
    (env : EnvironmentSequence Unit Unit) (r : Nat) :
    ScalingSafety.ResidueLTL.viewResidues env r =
      (ScalingSafety.ResidueLTL.mod3 (ScalingSafety.coordinate
        (evaluate (BlockEmbedding.graphPrefix (fun n => (env n).graph) r)).one),
       ScalingSafety.ResidueLTL.mod3 (ScalingSafety.coordinate
        (evaluate (BlockEmbedding.graphPrefix (fun n => (env n).graph) r)).two)) := by
  let dummy : StrategyPair Unit Unit Unit Unit := ⟨fun _ => (),fun _ => ()⟩
  have a := ScalingSafety.ResidueLTL.execution_views dummy env r
  have b := GraphExecutions.execution_views dummy env r
  change viewPair (executionPrefix dummy env r) = _ at a
  have same := a.symm.trans b
  simp only [ScalingSafety.ResidueLTL.viewResidues,same]

/-- C0 is exactly the position formula on every execution. -/
theorem row_position_iff (σ : StrategyPair Unit Unit (Output Q) (Output Q)) :
    (∀ h : List Graph, 0 < h.length →
      (σ.one (evaluate h).one).residue = ScalingSafety.ResidueLTL.mod3 (ScalingSafety.coordinate (evaluate h).one) ∧
      (σ.two (evaluate h).two).residue = ScalingSafety.ResidueLTL.mod3 (ScalingSafety.coordinate (evaluate h).two)) ↔
    ∀ env, ResidueValid (execution σ env) := by
  have row (env : EnvironmentSequence Unit Unit) (n : Nat) := GraphExecutions.execution_outputs σ env n
  constructor
  · intro positions env
    have coord (n : Nat) : residues (execution σ env n) = ScalingSafety.ResidueLTL.viewResidues env (n+1) := by
      rw [viewResidues_row]
      exact Prod.ext ((congrArg Output.residue (row env n).1).trans (positions _ (by simp [BlockEmbedding.prefix_length])).1)
        ((congrArg Output.residue (row env n).2).trans (positions _ (by simp [BlockEmbedding.prefix_length])).2)
    constructor
    · rw [coord,ScalingSafety.ResidueLTL.viewResidues_succ,GraphExecutions.execution_graph]
      rfl
    · intro n
      rw [coord,coord,ScalingSafety.ResidueLTL.viewResidues_succ,GraphExecutions.execution_graph]
  · intro position h positive
    have coord := position_coordinates σ (GraphExecutions.extend h) (position _) (h.length-1)
    rw [viewResidues_row,show h.length-1+1 = h.length by omega,
      GraphExecutions.extend_prefix h h.length le_rfl,List.take_length] at coord
    obtain ⟨one,two⟩ := GraphExecutions.extend_outputs σ h positive
    simpa only [residues,one,two,Prod.mk.injEq] using coord

/-- Forward implication, assembled from the separate manuscript-clause proofs. -/
theorem checks_global_rows [DecidableEq Q] (M : Machine Q)
    (σ : StrategyPair Unit Unit (Output Q) (Output Q))
    (checks : ∀ env, Checks M (execution σ env)) : GlobalRows M σ ∧ NoHaltingOutputs M σ := by
  have position := fun env => (checks env).position
  have agreement := fun env n => (checks env).agreement n
  have zero := fun env n => (checks env).zeroWeight n
  have left := fun env n => (checks env).leftBoundary n
  have right := fun env n => (checks env).rightBoundary n
  have transition := fun env n => (checks env).transition n
  refine ⟨⟨(row_position_iff σ).mpr position,agreement_row_uniform σ agreement,
    local_sum_on_view_edge M σ position (fun env n => (checks env).balance n),
    zero_claim_on_row σ position agreement zero left right,
    initial_check_on_row M σ position agreement zero left right (fun env => (checks env).initial),
    transition_leftmost_control M σ transition,transition_child_weight M σ position transition⟩,?_⟩
  intro h positive
  obtain ⟨one,two⟩ := GraphExecutions.extend_outputs σ h positive
  have live := (checks (GraphExecutions.extend h)).live (h.length-1)
  have agree := (checks (GraphExecutions.extend h)).agreement (h.length-1)
  simp only [Agreement,one,two] at live agree
  exact ⟨live,by rw [← agree.1]; exact live⟩

private theorem prefix_of_constant (env : EnvironmentSequence Unit Unit) (n : Nat) (g : Graph)
    (constant : ∀ t, t ≤ n → (env t).graph = g) :
    BlockEmbedding.graphPrefix (fun t => (env t).graph) (n+1) = List.replicate (n+1) g := by
  induction n with
  | zero => simp [BlockEmbedding.graphPrefix,constant 0 (by omega)]
  | succ n ih =>
    rw [BlockEmbedding.prefix_succ,List.replicate_succ',ih (fun t ht => constant t (by omega)),constant (n+1) (by omega)]


/-- Reverse implication: the global C0--C5 conditions force all formula
clauses. Initialization uses only the first edge's weight, not a plan at
the unused final endpoint. -/
theorem GlobalRows.checks [DecidableEq Q] {M : Machine Q}
    {σ : StrategyPair Unit Unit (Output Q) (Output Q)}
    (rows : GlobalRows M σ) (live : NoHaltingOutputs M σ)
    (env : EnvironmentSequence Unit Unit) : Checks M (execution σ env) := by
  have position := (row_position_iff σ).mp rows.position
  have uniform (n : Nat) := rows.uniform n
  have agreement (n : Nat) : Agreement (execution σ env n) := by
    obtain ⟨q,z,all⟩ := uniform n
    have eq := all (BlockEmbedding.graphPrefix (fun t => (env t).graph) (n+1)) (by simp)
    obtain ⟨one,two⟩ := GraphExecutions.execution_outputs σ env n
    exact ⟨by rw [one,two,eq.1,eq.2.1],by rw [one,two,eq.2.2.1,eq.2.2.2]⟩
  have edge (n : Nat) := execution_view_edge_labels σ env (position env) n
    (BlockEmbedding.graphPrefix (fun t => (env t).graph) (n+1)) rfl
  refine ⟨position env,agreement,?_,?_,?_,?_,?_,?_,?_⟩
  · intro n k
    rw [(edge n).1,(edge n).2]
    exact rows.balance _ (by simp) k
  · intro n k zero
    obtain ⟨q,z,all⟩ := uniform n
    have first := all (List.replicate (n+1) .right) (by simp)
    have current := all (BlockEmbedding.graphPrefix (fun t => (env t).graph) (n+1)) (by simp)
    have common : (Rows.emit (projectStrategy σ) (FullViewPath.left
        (evaluate (BlockEmbedding.graphPrefix (fun t => (env t).graph) (n+1))))).zero = z := by
      cases flag : (evaluate (BlockEmbedding.graphPrefix (fun t => (env t).graph) (n+1))).oneLeft <;>
        simp [FullViewPath.left,flag,Rows.emit,projectStrategy,current.2.2.1,current.2.2.2]
    rw [(edge n).1] at zero ⊢
    exact (rows.zero n k).2.2.1 (by rw [first.2.2.1,← common]; exact zero) _ (by simp)
  · intro n constant
    have pref := prefix_of_constant env n .right (by simpa only [GraphExecutions.execution_graph] using constant)
    rw [(GraphExecutions.execution_outputs σ env n).1,pref]
    exact ⟨fun k => (rows.zero n k).1,fun k => (rows.zero n k).2.2.2⟩
  · intro n constant
    have pref := prefix_of_constant env n .left (by simpa only [GraphExecutions.execution_graph] using constant)
    rw [(GraphExecutions.execution_outputs σ env n).2,pref]
    exact fun k => (rows.zero n k).2.1
  · obtain ⟨q,z,all⟩ := uniform 0
    have first := all [.right] rfl
    have current := all (BlockEmbedding.graphPrefix (fun t => (env t).graph) 1) (by simp)
    have firstTrue (k : Fin 2) : (σ.one (evaluate [.right]).one).base.zero k = true := by
      cases eq : (σ.one (evaluate [.right]).one).base.zero k with
      | true => rfl
      | false =>
        have zero := (rows.zero 0 k).2.2.2 eq
        have one := (rows.initial [.right] rfl).2.2 k
        change ((σ.one (evaluate [.right]).one).base.right k).weight.val = 1 at one
        change ((σ.one (evaluate [.right]).one).base.right k).weight.val = 0 at zero
        omega
    refine ⟨?_,?_⟩
    · rw [(GraphExecutions.execution_outputs σ env 0).1]
      exact (rows.initial _ (by simp)).1
    · intro k
      rw [(GraphExecutions.execution_outputs σ env 0).1,current.2.2.1,← first.2.2.1]
      exact firstTrue k
  · intro n
    obtain ⟨q,z,all⟩ := uniform n
    obtain ⟨q',z',all'⟩ := uniform (n+1)
    have current := all (BlockEmbedding.graphPrefix (fun t => (env t).graph) (n+1)) (by simp)
    have next := all' (BlockEmbedding.graphPrefix (fun t => (env t).graph) (n+1+1)) (by simp)
    have first := all (List.replicate (n+1) .right) (by simp)
    have firstNext := all' (List.replicate (n+2) .right) (by simp [Nat.add_assoc])
    constructor
    · rw [(GraphExecutions.execution_outputs σ env n).1,(GraphExecutions.execution_outputs σ env (n+1)).1,
        current.1,current.2.2.1,next.1,← first.1,← first.2.2.1,← firstNext.1]
      exact rows.control n
    · intro k
      rw [(edge n).1,(edge (n+1)).1,position_decodes_view_orientation σ env (position env),
        GraphExecutions.execution_graph,BlockEmbedding.prefix_succ]
      exact rows.children _ (by simp) (env (n+1)).graph k
  · intro n
    rw [(GraphExecutions.execution_outputs σ env n).1]
    exact (live _ (by simp)).1

/-- Exact global-row equivalence for the existing two-counter alphabet.
The separate one-counter transport is needed for the smaller displayed tuple. -/
theorem global_rows_iff_checks [DecidableEq Q] (M : Machine Q)
    (σ : StrategyPair Unit Unit (Output Q) (Output Q)) :
    (GlobalRows M σ ∧ NoHaltingOutputs M σ) ↔ ∀ env, Checks M (execution σ env) :=
  ⟨fun h => h.1.checks h.2,checks_global_rows M σ⟩

end DistributedSynthesis.CounterMachine.Paper
