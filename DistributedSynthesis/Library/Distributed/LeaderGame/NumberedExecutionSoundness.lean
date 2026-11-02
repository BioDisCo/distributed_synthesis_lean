/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.NumberedInitialState

/-! The concrete numbered game is sound for physical executions with finite
private input alphabets. Physical rounds and all objective priorities are
preserved by the decoder. -/
namespace Characterisation
open DistributedSynthesis

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
variable (small : ∀ k : EnvHistory I₁ I₂, P (History.graphSequence k) → leaderBoundary P d k = true →
  Nat.card (InputHistoryComponent P k) ≤ B)

include rankExact closed recognizes recent bounded small in
theorem numberedGame_execution_soundness
    (initial : NumberedSuccessorChoice (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)
    (initialRep : NumberedBoundaryRep M objective P (fun _ => objective.initial) initial.1.1 initial.2
      (boundaryOrigin P ([] : EnvHistory I₁ I₂)))
    (tree : LabeledTree
      (NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)
      (NumberedLeaderMove (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective))
    (accepted : (numberedLeaderGame M objective rank initial.1 (numberedGameInitialCode objective rank initial)).WinningTree tree) :
    ∃ σ : StrategyPair I₁ I₂ O₁ O₂, ∀ env : EnvironmentSequence I₁ I₂,
      (∀ n, P (branchNode (fun t => (env t).graph) n)) →
      objective.Accepts (fun n => recordContinuationLetter (execution σ env n)) := by
  obtain ⟨σ,winning⟩ := numberedGame_winning_strategy M objective rank rankExact P closed recognizes recent bounded small
    initial initialRep tree accepted
  refine ⟨σ,?_⟩
  intro env live
  let round := fun n => (⟨(env n).inputOne,(env n).inputTwo,(env n).graph,(),()⟩ : RoundRecord I₁ I₂ Graph Unit Unit)
  let history := branchNode round
  have depth : ∀ n, List.length (history n) = n := TreeNonemptiness.branch_length round
  have prefixes : ∀ m n, m ≤ n → (history n).take m = history m := take_branchNode round
  have graph : ∀ n, History.graphSequence (history n) = branchNode (fun t => (env t).graph) n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      simpa only [history,branchNode,History.graphSequence,List.map_append,List.map_singleton] using
        congrArg (fun w => w ++ [(env n).graph]) ih
  have physical := winning history depth prefixes (fun n => by rw [graph]; exact live n) round (fun _ => rfl)
  let input := fun n => EnvironmentRound.toProd (env n)
  have histories : ∀ n,
      (branchNode input n).map (fun r => (⟨r.1,r.2.1,r.2.2,(),()⟩ : RoundRecord I₁ I₂ Graph Unit Unit)) = history n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp only [branchNode,List.map_append,List.map_singleton,ih]; rfl
  have runs : ∀ n, objective.runFrom objective.initial
      (fun t => recordContinuationLetter (execution σ env t)) n =
      strategyHistoryLabel σ (fun s input output => objective.step s (input,output)) objective.initial (history n) := by
    intro n
    rw [← emptyContinuation_trace_execution]
    rw [continuationRun_strategy,histories]
    rfl
  have shifted : NatSeqMinEvenParity (fun n => objective.priority
      (objective.runFrom objective.initial (fun t => recordContinuationLetter (execution σ env t)) (1+n))) := by
    simpa only [runs,Nat.add_comm 1] using physical
  exact (natSeqMinEvenParity_shift _ 1).mp shifted

end
end Characterisation
