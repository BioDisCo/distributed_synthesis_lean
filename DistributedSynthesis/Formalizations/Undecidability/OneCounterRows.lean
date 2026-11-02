/- Project authors: see AUTHORS.md at the repository root. -/
import DistributedSynthesis.Formalizations.Undecidability.OneCounterTransport

namespace DistributedSynthesis.CounterMachine.OneCounter
open Characterisation FullViewPath
variable {Q : Type*}

def rowOutput (σ : StrategyPair Unit Unit (Output Q) (Output Q)) : Vertex → Output Q :=
  Sum.elim σ.one σ.two

/-- Scalar C0--C5, with the exact five-component manuscript output and
actual local-view vertices. Only the three edge weights, not the last
vertex's unused plan, are required to equal one in the initial row. -/
structure GlobalRows (M : Machine Q) (σ : StrategyPair Unit Unit (Output Q) (Output Q)) : Prop where
  position : ∀ h : List Graph, 0 < h.length →
    (σ.one (evaluate h).one).residue = ScalingSafety.ResidueLTL.mod3 (ScalingSafety.coordinate (evaluate h).one) ∧
    (σ.two (evaluate h).two).residue = ScalingSafety.ResidueLTL.mod3 (ScalingSafety.coordinate (evaluate h).two)
  uniform : ∀ n, ∃ q : Q, ∃ z : Bool, ∀ h : List Graph, h.length = n+1 →
    (σ.one (evaluate h).one).control = q ∧ (σ.two (evaluate h).two).control = q ∧
    (σ.one (evaluate h).one).zero = z ∧ (σ.two (evaluate h).two).zero = z
  balance : ∀ h : List Graph, 0 < h.length →
    let l := rowOutput σ (FullViewPath.left (evaluate h))
    let r := rowOutput σ (FullViewPath.right (evaluate h))
    l.right.promised + l.carry.val = (op M l.control l.zero).factor * l.right.weight.val + r.carry.val
  zero : ∀ n,
    let first := σ.one (evaluate (List.replicate (n+1) .right)).one
    let last := σ.two (evaluate (List.replicate (n+1) .left)).two
    first.carry.val = 0 ∧ last.carry.val = 0 ∧
    (first.zero = true → ∀ h : List Graph, h.length = n+1 →
      (rowOutput σ (FullViewPath.left (evaluate h))).right.weight.val = 1) ∧
    (first.zero = false → first.right.weight.val = 0)
  initial : ∀ h : List Graph, h.length = 1 →
    (σ.one (evaluate h).one).control = M.initial ∧
    (σ.two (evaluate h).two).control = M.initial ∧
    (rowOutput σ (FullViewPath.left (evaluate h))).right.weight.val = 1
  control : ∀ n,
    (σ.one (evaluate (List.replicate (n+2) .right)).one).control =
      next M (σ.one (evaluate (List.replicate (n+1) .right)).one).control
        (σ.one (evaluate (List.replicate (n+1) .right)).one).zero
  children : ∀ h : List Graph, 0 < h.length → ∀ g,
    (rowOutput σ (FullViewPath.left (evaluate (h++[g])))).right.weight =
      (rowOutput σ (FullViewPath.left (evaluate h))).right.child
        (ScalingSafety.digit (evaluate h).oneLeft g)

def NoHaltingOutputs (M : Machine Q) (σ : StrategyPair Unit Unit (Output Q) (Output Q)) : Prop :=
  ∀ h : List Graph, 0 < h.length → M.code (σ.one (evaluate h).one).control ≠ none ∧
    M.code (σ.two (evaluate h).two).control ≠ none

theorem rowOutput_embed (σ : StrategyPair Unit Unit (Output Q) (Output Q)) (v : Vertex) :
    Rows.emit (ResidueLTL.projectStrategy (mapStrategy embed embed σ)) v = (embed (rowOutput σ v)).base := by
  cases v <;> rfl

/-- Scalar rows and their inert-second-counter embedding satisfy exactly
the same structural conditions. -/
theorem global_rows_embed_iff [DecidableEq Q] (M : Machine Q) (single : OnlyFirst M)
    (σ : StrategyPair Unit Unit (Output Q) (Output Q)) :
    Paper.GlobalRows M (mapStrategy embed embed σ) ↔ GlobalRows M σ := by
  constructor
  · intro rows
    constructor
    · exact rows.position
    · intro n
      obtain ⟨q,z,all⟩ := rows.uniform n
      refine ⟨q,z 0,fun h len => ?_⟩
      have eq := all h len
      exact ⟨eq.1,eq.2.1,congrFun eq.2.2.1 0,congrFun eq.2.2.2 0⟩
    · intro h positive
      have balance := rows.balance h positive 0
      simpa only [rowOutput_embed] using balance
    · intro n
      have zero := rows.zero n 0
      simpa only [rowOutput_embed] using zero
    · intro h len
      have initial := rows.initial h len
      exact ⟨initial.1,initial.2.1,by simpa only [rowOutput_embed] using initial.2.2 0⟩
    · exact rows.control
    · intro h positive g
      simpa only [rowOutput_embed] using rows.children h positive g 0
  · intro rows
    constructor
    · exact rows.position
    · intro n
      obtain ⟨q,z,all⟩ := rows.uniform n
      refine ⟨q,zeroFlags z,fun h len => ?_⟩
      have eq := all h len
      exact ⟨eq.1,eq.2.1,congrArg zeroFlags eq.2.2.1,congrArg zeroFlags eq.2.2.2⟩
    · intro h positive k
      simp only [rowOutput_embed]
      fin_cases k
      · exact rows.balance h positive
      · simp [embed,dummyPlan,Plan.promised,op_second M single,TernaryCounter.Operation.factor]
    · intro n k
      simp only [rowOutput_embed]
      fin_cases k
      · exact rows.zero n
      · simp [mapStrategy,embed,zeroFlags,dummyPlan]
    · intro h len
      refine ⟨(rows.initial h len).1,(rows.initial h len).2.1,?_⟩
      intro k
      simp only [rowOutput_embed]
      fin_cases k
      · exact (rows.initial h len).2.2
      · rfl
    · exact rows.control
    · intro h positive g k
      simp only [rowOutput_embed]
      fin_cases k
      · exact rows.children h positive g
      · rfl

/-- Literal scalar form of the manuscript's global equivalence. -/
theorem global_rows_iff_checks [DecidableEq Q] (M : Machine Q) (single : OnlyFirst M)
    (σ : StrategyPair Unit Unit (Output Q) (Output Q)) :
    (GlobalRows M σ ∧ NoHaltingOutputs M σ) ↔ ∀ env, Checks M (execution σ env) := by
  have environment (env : EnvironmentSequence Unit Unit) :
      execution (mapStrategy embed embed σ) env = OmegaWord.map (mapRecord embed embed) (execution σ env) := by
    have same : env = GraphExecutions.ofGraphs (fun n => (env n).graph) := by
      funext n
      cases h : env n
      simp [GraphExecutions.ofGraphs,h]
    rw [same]
    exact mapStrategy_execution embed embed σ _
  rw [← global_rows_embed_iff M single σ]
  change (Paper.GlobalRows M (mapStrategy embed embed σ) ∧
    Paper.NoHaltingOutputs M (mapStrategy embed embed σ)) ↔ _
  rw [Paper.global_rows_iff_checks]
  apply forall_congr'
  intro env
  rw [environment]
  exact checks_embed_iff M single _

theorem global_rows_iff_formula [DecidableEq Q] [Fintype Q]
    (M : Machine Q) (single : OnlyFirst M)
    (σ : StrategyPair Unit Unit (Output Q) (Output Q)) :
    (GlobalRows M σ ∧ NoHaltingOutputs M σ) ↔
      ∀ env, LTL.Satisfies FiniteLetterLTL.interp (execution σ env) (formula M) :=
  (global_rows_iff_checks M single σ).trans (forall_congr' (fun env => (satisfies_iff M (execution σ env)).symm))

theorem position_rows (σ : StrategyPair Unit Unit (Output Q) (Output Q))
    (position : ∀ env, Position (execution σ env)) :
    ∀ h : List Graph, 0 < h.length →
      (σ.one (evaluate h).one).residue = ScalingSafety.ResidueLTL.mod3 (ScalingSafety.coordinate (evaluate h).one) ∧
      (σ.two (evaluate h).two).residue = ScalingSafety.ResidueLTL.mod3 (ScalingSafety.coordinate (evaluate h).two) := by
  apply (Paper.row_position_iff (mapStrategy embed embed σ)).mpr
  intro env
  rw [map_execution]
  exact (position_embed_iff _).mpr (position env)

theorem agreement_row_uniform (σ : StrategyPair Unit Unit (Output Q) (Output Q))
    (agreement : ∀ env n, Agreement (execution σ env n)) (n : Nat) :
    ∃ q : Q, ∃ z : Bool, ∀ h : List Graph, h.length = n+1 →
      (σ.one (evaluate h).one).control = q ∧ (σ.two (evaluate h).two).control = q ∧
      (σ.one (evaluate h).one).zero = z ∧ (σ.two (evaluate h).two).zero = z := by
  have lifted : ∀ env n, Paper.Agreement (execution (mapStrategy embed embed σ) env n) := by
    intro env n
    rw [map_execution]
    exact (agreement_embed_iff _).mpr (agreement env n)
  obtain ⟨q,z,all⟩ := Paper.agreement_row_uniform _ lifted n
  exact ⟨q,z 0,fun h len => ⟨(all h len).1,(all h len).2.1,
    congrFun (all h len).2.2.1 0,congrFun (all h len).2.2.2 0⟩⟩

theorem local_sum_on_view_edge [DecidableEq Q] (M : Machine Q) (single : OnlyFirst M)
    (σ : StrategyPair Unit Unit (Output Q) (Output Q))
    (position : ∀ env, Position (execution σ env))
    (balance : ∀ env n, Balance M (execution σ env n))
    (h : List Graph) (positive : 0 < h.length) :
    let l := rowOutput σ (FullViewPath.left (evaluate h))
    let r := rowOutput σ (FullViewPath.right (evaluate h))
    l.right.promised + l.carry.val = (op M l.control l.zero).factor * l.right.weight.val + r.carry.val := by
  have liftedPosition : ∀ env, ResidueLTL.ResidueValid (execution (mapStrategy embed embed σ) env) := by
    intro env; rw [map_execution]; exact (position_embed_iff _).mpr (position env)
  have liftedBalance : ∀ env n, Paper.Balance M (execution (mapStrategy embed embed σ) env n) := by
    intro env n; rw [map_execution]; exact (balance_embed_iff M single _).mpr (balance env n)
  simpa only [rowOutput_embed] using
    Paper.local_sum_on_view_edge M (mapStrategy embed embed σ) liftedPosition liftedBalance h positive 0

theorem zero_claim_on_row [DecidableEq Q]
    (σ : StrategyPair Unit Unit (Output Q) (Output Q))
    (position : ∀ env, Position (execution σ env))
    (agreement : ∀ env n, Agreement (execution σ env n))
    (zeroWeight : ∀ env n, ZeroWeight (execution σ env n))
    (leftBoundary : ∀ env n, (∀ t, t ≤ n → (execution σ env t).graph = .right) → LeftBoundary (execution σ env n))
    (rightBoundary : ∀ env n, (∀ t, t ≤ n → (execution σ env t).graph = .left) → RightBoundary (execution σ env n))
    (n : Nat) :
    let first := σ.one (evaluate (List.replicate (n+1) .right)).one
    let last := σ.two (evaluate (List.replicate (n+1) .left)).two
    first.carry.val = 0 ∧ last.carry.val = 0 ∧
    (first.zero = true → ∀ h : List Graph, h.length = n+1 →
      (rowOutput σ (FullViewPath.left (evaluate h))).right.weight.val = 1) ∧
    (first.zero = false → first.right.weight.val = 0) := by
  have liftedPosition : ∀ env, ResidueLTL.ResidueValid (execution (mapStrategy embed embed σ) env) := by
    intro env; rw [map_execution]; exact (position_embed_iff _).mpr (position env)
  have liftedAgreement : ∀ env n, Paper.Agreement (execution (mapStrategy embed embed σ) env n) := by
    intro env n; rw [map_execution]; exact (agreement_embed_iff _).mpr (agreement env n)
  have liftedZero : ∀ env n, Paper.ZeroWeight (execution (mapStrategy embed embed σ) env n) := by
    intro env n; rw [map_execution]; exact (zeroWeight_embed_iff _).mpr (zeroWeight env n)
  have liftedLeft : ∀ env n, (∀ t, t ≤ n → (execution (mapStrategy embed embed σ) env t).graph = .right) →
      ResidueLTL.leftCheck (execution (mapStrategy embed embed σ) env n).outputOne.base := by
    intro env n constant; rw [map_execution] at constant ⊢
    exact (leftBoundary_embed_iff _).mpr (leftBoundary env n constant)
  have liftedRight : ∀ env n, (∀ t, t ≤ n → (execution (mapStrategy embed embed σ) env t).graph = .left) →
      ResidueLTL.rightCheck (execution (mapStrategy embed embed σ) env n).outputTwo.base := by
    intro env n constant; rw [map_execution] at constant ⊢
    exact (rightBoundary_embed_iff _).mpr (rightBoundary env n constant)
  simpa only [rowOutput_embed] using Paper.zero_claim_on_row (mapStrategy embed embed σ)
    liftedPosition liftedAgreement liftedZero liftedLeft liftedRight n 0

theorem initial_check_on_row [DecidableEq Q] (M : Machine Q)
    (σ : StrategyPair Unit Unit (Output Q) (Output Q))
    (position : ∀ env, Position (execution σ env))
    (agreement : ∀ env n, Agreement (execution σ env n))
    (zeroWeight : ∀ env n, ZeroWeight (execution σ env n))
    (leftBoundary : ∀ env n, (∀ t, t ≤ n → (execution σ env t).graph = .right) → LeftBoundary (execution σ env n))
    (rightBoundary : ∀ env n, (∀ t, t ≤ n → (execution σ env t).graph = .left) → RightBoundary (execution σ env n))
    (initial : ∀ env, Initial M (execution σ env 0)) :
    ∀ h : List Graph, h.length = 1 →
      (σ.one (evaluate h).one).control = M.initial ∧ (σ.two (evaluate h).two).control = M.initial ∧
      (rowOutput σ (FullViewPath.left (evaluate h))).right.weight.val = 1 := by
  have liftedPosition : ∀ env, ResidueLTL.ResidueValid (execution (mapStrategy embed embed σ) env) := by
    intro env; rw [map_execution]; exact (position_embed_iff _).mpr (position env)
  have liftedAgreement : ∀ env n, Paper.Agreement (execution (mapStrategy embed embed σ) env n) := by
    intro env n; rw [map_execution]; exact (agreement_embed_iff _).mpr (agreement env n)
  have liftedZero : ∀ env n, Paper.ZeroWeight (execution (mapStrategy embed embed σ) env n) := by
    intro env n; rw [map_execution]; exact (zeroWeight_embed_iff _).mpr (zeroWeight env n)
  have liftedLeft : ∀ env n, (∀ t, t ≤ n → (execution (mapStrategy embed embed σ) env t).graph = .right) →
      ResidueLTL.leftCheck (execution (mapStrategy embed embed σ) env n).outputOne.base := by
    intro env n constant; rw [map_execution] at constant ⊢
    exact (leftBoundary_embed_iff _).mpr (leftBoundary env n constant)
  have liftedRight : ∀ env n, (∀ t, t ≤ n → (execution (mapStrategy embed embed σ) env t).graph = .left) →
      ResidueLTL.rightCheck (execution (mapStrategy embed embed σ) env n).outputTwo.base := by
    intro env n constant; rw [map_execution] at constant ⊢
    exact (rightBoundary_embed_iff _).mpr (rightBoundary env n constant)
  have liftedInitial : ∀ env, Paper.Initial M (execution (mapStrategy embed embed σ) env 0) := by
    intro env; rw [map_execution]; exact (initial_embed_iff M _).mpr (initial env)
  intro h len
  obtain ⟨one,two,weight⟩ := Paper.initial_check_on_row M (mapStrategy embed embed σ)
    liftedPosition liftedAgreement liftedZero liftedLeft liftedRight liftedInitial h len
  exact ⟨one,two,by simpa only [rowOutput_embed] using weight 0⟩

theorem transition_child_weight [DecidableEq Q] (M : Machine Q)
    (σ : StrategyPair Unit Unit (Output Q) (Output Q))
    (position : ∀ env, Position (execution σ env))
    (transition : ∀ env n, Transition M (execution σ env n) (execution σ env (n+1)))
    (h : List Graph) (positive : 0 < h.length) (g : Graph) :
    (rowOutput σ (FullViewPath.left (evaluate (h++[g])))).right.weight =
      (rowOutput σ (FullViewPath.left (evaluate h))).right.child
        (ScalingSafety.digit (evaluate h).oneLeft g) := by
  have liftedPosition : ∀ env, ResidueLTL.ResidueValid (execution (mapStrategy embed embed σ) env) := by
    intro env; rw [map_execution]; exact (position_embed_iff _).mpr (position env)
  have liftedTransition : ∀ env n, Paper.Transition M (execution (mapStrategy embed embed σ) env n)
      (execution (mapStrategy embed embed σ) env (n+1)) := by
    intro env n; rw [map_execution]; exact (transition_embed_iff M _ _).mpr (transition env n)
  simpa only [rowOutput_embed] using Paper.transition_child_weight M (mapStrategy embed embed σ)
    liftedPosition liftedTransition h positive g 0

theorem transition_leftmost_control (M : Machine Q)
    (σ : StrategyPair Unit Unit (Output Q) (Output Q))
    (transition : ∀ env n, Transition M (execution σ env n) (execution σ env (n+1))) (n : Nat) :
    (σ.one (evaluate (List.replicate (n+2) .right)).one).control =
      next M (σ.one (evaluate (List.replicate (n+1) .right)).one).control
        (σ.one (evaluate (List.replicate (n+1) .right)).one).zero := by
  have liftedTransition : ∀ env n, Paper.Transition M (execution (mapStrategy embed embed σ) env n)
      (execution (mapStrategy embed embed σ) env (n+1)) := by
    intro env n; rw [map_execution]; exact (transition_embed_iff M _ _).mpr (transition env n)
  exact Paper.transition_leftmost_control M (mapStrategy embed embed σ) liftedTransition n

end DistributedSynthesis.CounterMachine.OneCounter
