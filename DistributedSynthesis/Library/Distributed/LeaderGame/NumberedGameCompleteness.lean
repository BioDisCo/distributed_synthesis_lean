/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.NumberedOriginalAssembly

/-! A physical winning strategy supplies a winning tree of the concrete
numbered game. All local successor and global parity premises are discharged
from that one strategy. -/
namespace Characterisation
open DistributedSynthesis

theorem executionWinning_physical_parity {I₁ I₂ O₁ O₂ : Type} {C : Nat}
    (objective : DetParityAutomaton (ContinuationLetter I₁ I₂ O₁ O₂))
    (rank : objective.State → Fin (C+1)) (rankExact : ∀ q, (rank q).val = objective.priority q)
    (σ : StrategyPair I₁ I₂ O₁ O₂)
    (winning : ∀ env, objective.Accepts (fun n => recordContinuationLetter (execution σ env n)))
    (physical : Nat → RoundRecord I₁ I₂ Graph Unit Unit) :
    NatSeqMinEvenParity (fun n => (rank (strategyHistoryLabel σ
      (fun s input output => objective.step s (input,output)) objective.initial (branchNode physical (n+1)))).val) := by
  let env : EnvironmentSequence I₁ I₂ := fun n => ⟨(physical n).inputOne,(physical n).inputTwo,(physical n).graph⟩
  let input := fun n => EnvironmentRound.toProd (env n)
  have histories : ∀ n,
      (branchNode input n).map (fun r => (⟨r.1,r.2.1,r.2.2,(),()⟩ : RoundRecord I₁ I₂ Graph Unit Unit)) = branchNode physical n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp only [branchNode,List.map_append,List.map_singleton,ih]; rfl
  have runs : ∀ n, objective.runFrom objective.initial
      (fun t => recordContinuationLetter (execution σ env t)) n =
      strategyHistoryLabel σ (fun s input output => objective.step s (input,output)) objective.initial (branchNode physical n) := by
    intro n
    rw [← emptyContinuation_trace_execution,continuationRun_strategy,histories]
    rfl
  have accepted : NatSeqMinEvenParity (fun n => objective.priority
      (objective.runFrom objective.initial (fun t => recordContinuationLetter (execution σ env t)) n)) := winning env
  have shifted := (natSeqMinEvenParity_shift _ 1).mpr accepted
  simpa only [runs,rankExact,Nat.add_comm 1] using shifted

section
variable {GQ I₁ I₂ O₁ O₂ : Type} {d K B C : Nat}
variable [Fintype GQ] [DecidableEq GQ]
variable [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
variable [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂]
variable [Inhabited I₁] [Inhabited I₂] [Inhabited O₁] [Inhabited O₂]
variable (M : Recognizer Graph GQ) [DecidablePred (· ∈ M.accept)]
variable (objective : DetParityAutomaton (ContinuationLetter I₁ I₂ O₁ O₂))
variable [DecidableEq objective.State] (rank : objective.State → Fin (C+1))
variable (rankExact : ∀ q, (rank q).val = objective.priority q)
variable (P : List Graph → Prop)
variable (closed : PrefixClosed P) (recognizes : ∀ g, P g ↔ M.eval g ∈ M.accept)
variable (recent : ∀ g, P g → ∃ p, RecentOther P d g p)
variable (bounded : ∀ g, P g → Finite (HistoryComponent P g) ∧ Nat.card (HistoryComponent P g) ≤ K)

include rankExact closed recognizes recent bounded in
theorem numberedGame_complete
    (initial : NumberedSuccessorChoice (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)
    (initialRep : NumberedBoundaryRep M objective P (fun _ => objective.initial) initial.1.1 initial.2
      (boundaryOrigin P ([] : EnvHistory I₁ I₂)))
    (live : P [])
    (σ : StrategyPair I₁ I₂ O₁ O₂)
    (winning : ∀ env, objective.Accepts (fun n => recordContinuationLetter (execution σ env n))) :
    ∃ table : RunParityTreeAutomaton.StateControlledTreeTable
        (numberedLeaderGame M objective rank initial.1 (numberedGameInitialCode objective rank initial)).toRunAutomaton,
      (numberedLeaderGame M objective rank initial.1 (numberedGameInitialCode objective rank initial)).WinningTree
        table.toTransitionRationalTree.labeledTree := by
  have rep : NumberedBoundaryRep M objective P
      (strategyHistoryLabel σ (fun s input output => objective.step s (input,output)) objective.initial)
      initial.1.1 initial.2 (boundaryOrigin P ([] : EnvHistory I₁ I₂)) := by
    refine ⟨initialRep.1,initialRep.2.1,initialRep.2.2.1,initialRep.2.2.2.1,initialRep.2.2.2.2.1,?_⟩
    intro i
    rw [initialRep.2.2.2.2.2 i,List.eq_nil_of_length_eq_zero (initialRep.2.2.1 i)]
    rfl
  let source : NumberedOriginalSource (d:=d) (K:=K) (B:=B) (C:=C) M objective P σ :=
    ⟨initial,[],live,leaderBoundary_empty P d,rep⟩
  exact numberedOriginal_finite_game M objective rank P σ closed recognizes recent bounded winning
    (executionWinning_physical_parity objective rank rankExact σ winning) source rfl
    (numberedGameInitialCode objective rank initial)

end
end Characterisation
