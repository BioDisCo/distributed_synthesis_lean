/- Project authors: see AUTHORS.md at the repository root. -/
import DistributedSynthesis.Formalizations.Undecidability.FormulaCorrespondence
import DistributedSynthesis.Library.Distributed.ViewAgreement
import DistributedSynthesis.Library.Distributed.GraphAdversaries.GeometryCoding

/-! Individual row implications of the manuscript's formula clauses.
These results deliberately do not assume `Winning` or the other checks. -/
namespace DistributedSynthesis.CounterMachine.Paper
open ResidueLTL FullViewPath
variable {Q : Type*}

/-- Path Agreement implies C1 on every row. The only formula premise is
agreement; Position Order, Local Sum, initialization, transitions, and
nonhalting are not assumed. -/
theorem agreement_row_uniform
    (σ : StrategyPair Unit Unit (Output Q) (Output Q))
    (agreement : ∀ env : EnvironmentSequence Unit Unit, ∀ n,
      Agreement (execution σ env n)) (n : Nat) :
    ∃ q : Q, ∃ z : Fin 2 → Bool, ∀ h : List Graph, h.length = n+1 →
      (σ.one (evaluate h).one).base.control = q ∧
      (σ.two (evaluate h).two).base.control = q ∧
      (σ.one (evaluate h).one).base.zero = z ∧
      (σ.two (evaluate h).two).base.zero = z := by
  obtain ⟨value, uniform⟩ := projected_execution_agreement_implies_uniform σ
    (fun o => (o.base.control, o.base.zero)) n
    (fun env => Prod.ext (agreement env n).1 (agreement env n).2)
  refine ⟨value.1, value.2, fun h len => ?_⟩
  obtain ⟨one, two⟩ := uniform h len
  exact ⟨congrArg Prod.fst one, congrArg Prod.fst two,
    congrArg Prod.snd one, congrArg Prod.snd two⟩

private theorem advance_orientation (s : Cell) (g : Graph) :
    (FullViewPath.advance s g).oneLeft = ScalingSafety.Source.turn s.oneLeft g := by
  cases g <;> rfl

/-- Position Order decodes the actual left endpoint of each execution edge,
independently of all other formula clauses. -/
theorem position_decodes_view_orientation
    (σ : StrategyPair Unit Unit (Output Q) (Output Q))
    (env : EnvironmentSequence Unit Unit)
    (position : ResidueValid (execution σ env)) (n : Nat) :
    oneLeft (execution σ env n) =
      (evaluate (BlockEmbedding.graphPrefix (fun k => (env k).graph) (n+1))).oneLeft := by
  apply ScalingSafety.ResidueLTL.oriented_decode
  induction n with
  | zero =>
    rw [position.1, GraphExecutions.execution_graph]
    exact ScalingSafety.ResidueLTL.oriented_update true (0,1) (env 0).graph (by rfl)
  | succ n ih =>
    rw [position.2 n, GraphExecutions.execution_graph, BlockEmbedding.prefix_succ,
      FullViewPath.at_append, advance_orientation]
    exact ScalingSafety.ResidueLTL.oriented_update _ _ _ ih

/-- Execution labels at a known finite graph prefix, with orientation
supplied only by Position Order. -/
theorem execution_view_edge_labels [DecidableEq Q]
    (σ : StrategyPair Unit Unit (Output Q) (Output Q))
    (env : EnvironmentSequence Unit Unit) (position : ResidueValid (execution σ env))
    (n : Nat) (h : List Graph)
    (pref : BlockEmbedding.graphPrefix (fun t => (env t).graph) (n+1) = h) :
    leftLabel (execution σ env n) =
      Rows.emit (projectStrategy σ) (FullViewPath.left (evaluate h)) ∧
    rightLabel (execution σ env n) =
      Rows.emit (projectStrategy σ) (FullViewPath.right (evaluate h)) := by
  have outputs := GraphExecutions.execution_outputs σ env n
  have orientation := position_decodes_view_orientation σ env position n
  rw [pref] at outputs orientation
  simp only [leftLabel, rightLabel, orientation]
  cases flag : (evaluate h).oneLeft <;>
    simp only [flag, Bool.false_eq_true, ↓reduceIte, outputs.1, outputs.2,
      FullViewPath.left, FullViewPath.right, Rows.emit, projectStrategy, Sum.elim_inl,
      Sum.elim_inr, and_self]

/-- The decoded execution labels are exactly the labels at the two actual
endpoints of the finite history in the existing view path. -/
theorem position_view_edge_labels [DecidableEq Q]
    (σ : StrategyPair Unit Unit (Output Q) (Output Q))
    (position : ∀ env, ResidueValid (execution σ env))
    (h : List Graph) (nonempty : 0 < h.length) :
    leftLabel (execution σ (GraphExecutions.extend h) (h.length-1)) =
      Rows.emit (projectStrategy σ) (FullViewPath.left (evaluate h)) ∧
    rightLabel (execution σ (GraphExecutions.extend h) (h.length-1)) =
      Rows.emit (projectStrategy σ) (FullViewPath.right (evaluate h)) := by
  apply execution_view_edge_labels σ (GraphExecutions.extend h)
    (position (GraphExecutions.extend h))
  rw [show h.length-1+1 = h.length by omega,
    GraphExecutions.extend_prefix h h.length le_rfl, List.take_length]

/-- Local Sum and Position Order imply C2 at each actual edge. The left
and right labels are those of the existing full-view path, not an assumed
orientation or a row certificate. -/
theorem local_sum_on_view_edge [DecidableEq Q]
    (M : Machine Q) (σ : StrategyPair Unit Unit (Output Q) (Output Q))
    (position : ∀ env, ResidueValid (execution σ env))
    (balance : ∀ env n, Balance M (execution σ env n))
    (h : List Graph) (nonempty : 0 < h.length) (k : Fin 2) :
    let l := Rows.emit (projectStrategy σ) (FullViewPath.left (evaluate h))
    let r := Rows.emit (projectStrategy σ) (FullViewPath.right (evaluate h))
    (l.right k).promised + (l.carry k).val =
      (M.op l.control l.zero k).factor * (l.right k).weight.val + (r.carry k).val := by
  have eq := balance (GraphExecutions.extend h) (h.length-1) k
  obtain ⟨left, right⟩ := position_view_edge_labels σ position h nonempty
  simpa only [left, right] using eq

/-- The two boundary clauses evaluated along the constant graph histories,
exactly as in the Zero Claim proof. -/
theorem zero_boundary_on_row
    (σ : StrategyPair Unit Unit (Output Q) (Output Q))
    (leftBoundary : ∀ env n, (∀ t, t ≤ n → (execution σ env t).graph = .right) →
      leftCheck (execution σ env n).outputOne.base)
    (rightBoundary : ∀ env n, (∀ t, t ≤ n → (execution σ env t).graph = .left) →
      rightCheck (execution σ env n).outputTwo.base) (n : Nat) :
    leftCheck (σ.one (evaluate (List.replicate (n+1) .right)).one).base ∧
    rightCheck (σ.two (evaluate (List.replicate (n+1) .left)).two).base := by
  have prefixGraph (g : Graph) (t : Nat) (before : t ≤ n) :
      (execution σ (GraphExecutions.extend (List.replicate (n+1) g)) t).graph = g := by
    rw [GraphExecutions.execution_graph]
    simp [GraphExecutions.extend, GraphExecutions.ofGraphs, List.getD,
      show t < n+1 by omega]
  have left := leftBoundary (GraphExecutions.extend (List.replicate (n+1) .right)) n
    (prefixGraph .right)
  have right := rightBoundary (GraphExecutions.extend (List.replicate (n+1) .left)) n
    (prefixGraph .left)
  have outputsL := GraphExecutions.extend_outputs σ (List.replicate (n+1) .right) (by simp)
  have outputsR := GraphExecutions.extend_outputs σ (List.replicate (n+1) .left) (by simp)
  simp only [List.length_replicate, Nat.add_sub_cancel] at outputsL outputsR
  rw [outputsL.1] at left
  rw [outputsR.2] at right
  exact ⟨left, right⟩

/-- Zero Claim, Path Agreement and Position Order imply C3. In particular,
no Local Sum, transition, initial-state or nonhalting premise is used. -/
theorem zero_claim_on_row [DecidableEq Q]
    (σ : StrategyPair Unit Unit (Output Q) (Output Q))
    (position : ∀ env, ResidueValid (execution σ env))
    (agreement : ∀ env n, Agreement (execution σ env n))
    (zeroWeight : ∀ env n, ZeroWeight (execution σ env n))
    (leftBoundary : ∀ env n, (∀ t, t ≤ n → (execution σ env t).graph = .right) →
      leftCheck (execution σ env n).outputOne.base)
    (rightBoundary : ∀ env n, (∀ t, t ≤ n → (execution σ env t).graph = .left) →
      rightCheck (execution σ env n).outputTwo.base) (n : Nat) (k : Fin 2) :
    let first := (σ.one (evaluate (List.replicate (n+1) .right)).one).base
    let last := (σ.two (evaluate (List.replicate (n+1) .left)).two).base
    (first.carry k).val = 0 ∧ (last.carry k).val = 0 ∧
    (first.zero k = true → ∀ h : List Graph, h.length = n+1 →
      ((Rows.emit (projectStrategy σ) (FullViewPath.left (evaluate h))).right k).weight.val = 1) ∧
    (first.zero k = false → (first.right k).weight.val = 0) := by
  obtain ⟨left, right⟩ := zero_boundary_on_row σ leftBoundary rightBoundary n
  refine ⟨left.1 k, right k, ?_, left.2 k⟩
  intro claimed h len
  obtain ⟨q, z, uniform⟩ := agreement_row_uniform σ agreement n
  have firstZero := (uniform (List.replicate (n+1) .right) (List.length_replicate ..)).2.2.1
  have trueZero : z k = true := by rw [← firstZero]; exact claimed
  obtain ⟨_, _, oneZero, twoZero⟩ := uniform h len
  have leftZero : (Rows.emit (projectStrategy σ) (FullViewPath.left (evaluate h))).zero k = true := by
    cases flag : (evaluate h).oneLeft <;>
      simp [FullViewPath.left, flag, Rows.emit, projectStrategy, oneZero, twoZero, trueZero]
  have check := zeroWeight (GraphExecutions.extend h) (h.length-1) k
  rw [(position_view_edge_labels σ position h (by omega)).1] at check
  exact check leftZero

/-- Initial Check together with Zero Claim, Path Agreement and Position
Order implies C4. Only the three edge weights are constrained; no weight
at the unused right endpoint is asserted. -/
theorem initial_check_on_row [DecidableEq Q]
    (M : Machine Q) (σ : StrategyPair Unit Unit (Output Q) (Output Q))
    (position : ∀ env, ResidueValid (execution σ env))
    (agreement : ∀ env n, Agreement (execution σ env n))
    (zeroWeight : ∀ env n, ZeroWeight (execution σ env n))
    (leftBoundary : ∀ env n, (∀ t, t ≤ n → (execution σ env t).graph = .right) →
      leftCheck (execution σ env n).outputOne.base)
    (rightBoundary : ∀ env n, (∀ t, t ≤ n → (execution σ env t).graph = .left) →
      rightCheck (execution σ env n).outputTwo.base)
    (initial : ∀ env, Initial M (execution σ env 0)) :
    ∀ h : List Graph, h.length = 1 →
      (σ.one (evaluate h).one).base.control = M.initial ∧
      (σ.two (evaluate h).two).base.control = M.initial ∧
      ∀ k, ((Rows.emit (projectStrategy σ) (FullViewPath.left (evaluate h))).right k).weight.val = 1 := by
  have firstInitial := initial (GraphExecutions.extend [.right])
  have firstOutputs := GraphExecutions.extend_outputs σ [.right] (by simp)
  simp only [List.length_singleton, Nat.sub_self] at firstOutputs
  unfold Initial at firstInitial
  rw [firstOutputs.1] at firstInitial
  obtain ⟨q, z, uniform⟩ := agreement_row_uniform σ agreement 0
  have firstControl := (uniform [.right] rfl).1
  have control : q = M.initial := firstControl.symm.trans firstInitial.1
  intro h len
  obtain ⟨one, two, _, _⟩ := uniform h len
  refine ⟨one.trans control, two.trans control, fun k => ?_⟩
  exact (zero_claim_on_row σ position agreement zeroWeight leftBoundary rightBoundary 0 k).2.2.1
    (firstInitial.2 k) h len

/-- The promised-child-weight part of C5 follows from Proper Transition and
Position Order alone, for every child of every nonempty history. -/
theorem transition_child_weight [DecidableEq Q]
    (M : Machine Q) (σ : StrategyPair Unit Unit (Output Q) (Output Q))
    (position : ∀ env, ResidueValid (execution σ env))
    (transition : ∀ env n, Transition M (execution σ env n) (execution σ env (n+1)))
    (h : List Graph) (nonempty : 0 < h.length) (g : Graph) (k : Fin 2) :
    let old := Rows.emit (projectStrategy σ) (FullViewPath.left (evaluate h))
    let next := Rows.emit (projectStrategy σ) (FullViewPath.left (evaluate (h++[g])))
    (next.right k).weight = (old.right k).child (ScalingSafety.digit (evaluate h).oneLeft g) := by
  let env := GraphExecutions.extend (h++[g])
  have pref : BlockEmbedding.graphPrefix (fun t => (env t).graph) (h.length-1+1) = h := by
    rw [show h.length-1+1 = h.length by omega]
    rw [GraphExecutions.extend_prefix (h++[g]) h.length (by simp), List.take_left]
  have prefNext : BlockEmbedding.graphPrefix (fun t => (env t).graph) (h.length+1) = h++[g] := by
    rw [GraphExecutions.extend_prefix (h++[g]) (h.length+1) (by simp)]
    simpa only [List.length_append, List.length_singleton] using
      (List.take_length : (h++[g]).take (h++[g]).length = h++[g])
  have old := (execution_view_edge_labels σ env (position env) (h.length-1) h pref).1
  have next := (execution_view_edge_labels σ env (position env) h.length (h++[g]) prefNext).1
  have orientation := position_decodes_view_orientation σ env (position env) (h.length-1)
  rw [pref] at orientation
  have step := (transition env (h.length-1)).2 k
  rw [show h.length-1+1 = h.length by omega, old, next, orientation,
    GraphExecutions.execution_graph] at step
  have graph : (env h.length).graph = g := by
    simpa only [List.append_nil] using GraphExecutions.extend_fault h [] g
  simpa only [graph] using step

/-- The control-state part of C5 concerns the leftmost vertex only. It
therefore follows from Proper Transition without Path Agreement. -/
theorem transition_leftmost_control
    (M : Machine Q) (σ : StrategyPair Unit Unit (Output Q) (Output Q))
    (transition : ∀ env n, Transition M (execution σ env n) (execution σ env (n+1))) (n : Nat) :
    let old := (σ.one (evaluate (List.replicate (n+1) .right)).one).base
    let next := (σ.one (evaluate (List.replicate (n+2) .right)).one).base
    next.control = M.next old.control old.zero := by
  let env := GraphExecutions.ofGraphs (fun _ => .right)
  have pref (r : Nat) : BlockEmbedding.graphPrefix (fun t => (env t).graph) r =
      List.replicate r .right := by
    simp [BlockEmbedding.graphPrefix, env, GraphExecutions.ofGraphs]
  have old := (GraphExecutions.execution_outputs σ env n).1
  have next := (GraphExecutions.execution_outputs σ env (n+1)).1
  rw [pref] at old next
  have step := (transition env n).1
  simpa only [old, next, Nat.add_assoc] using step

/-- The child digit used by Proper Transition is the actual offset of the
edge in the reflected view-path order. -/
theorem child_index_eq (h : List Graph) (g : Graph) :
    Characterisation.pathIndex (h++[g]) = 3 * Characterisation.pathIndex h +
      (ScalingSafety.digit (evaluate h).oneLeft g).val := by
  rw [Characterisation.pathIndex_append, Characterisation.orientation_agrees]
  have parity : Characterisation.pathIndex h % 2 = 0 ∨ Characterisation.pathIndex h % 2 = 1 := by omega
  rcases parity with hp | hp <;> cases g <;>
    simp [Characterisation.indexStep, Characterisation.graphDigit, ScalingSafety.digit, hp]

/-- The literal all-three-offsets form of the weight clause in C5. Every
position 3j+x occurs and carries exactly the parent promise a_x. -/
theorem transition_weight_at_child_position [DecidableEq Q]
    (M : Machine Q) (σ : StrategyPair Unit Unit (Output Q) (Output Q))
    (position : ∀ env, ResidueValid (execution σ env))
    (transition : ∀ env n, Transition M (execution σ env n) (execution σ env (n+1)))
    (h : List Graph) (nonempty : 0 < h.length) (k : Fin 2) (d : Fin 3) :
    ∃ g : Graph, Characterisation.pathIndex (h++[g]) = 3 * Characterisation.pathIndex h + d.val ∧
      ((Rows.emit (projectStrategy σ) (FullViewPath.left (evaluate (h++[g])))).right k).weight =
        ((Rows.emit (projectStrategy σ) (FullViewPath.left (evaluate h))).right k).child d := by
  obtain ⟨g, index⟩ := Characterisation.indexStep_surjective_digit (Characterisation.pathIndex h) d.val d.isLt
  have actual : Characterisation.pathIndex (h++[g]) = 3 * Characterisation.pathIndex h + d.val := by
    rw [Characterisation.pathIndex_append, index]
  have digit : ScalingSafety.digit (evaluate h).oneLeft g = d := by
    apply Fin.ext
    have := child_index_eq h g
    omega
  refine ⟨g, actual, ?_⟩
  simpa only [digit] using transition_child_weight M σ position transition h nonempty g k

end DistributedSynthesis.CounterMachine.Paper
