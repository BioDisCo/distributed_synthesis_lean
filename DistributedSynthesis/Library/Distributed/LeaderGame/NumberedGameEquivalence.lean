/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.NumberedGameCompleteness

/-! Exact semantic reduction to the concrete finite numbered game. The
objective accepts every execution that leaves the graph prefix language;
for synthesis it is the existing guarded LTL objective. Uniform computability
of the instance-to-game encoding is a separate obligation. -/
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
variable (live : P [])
variable (escape : ∀ (σ : StrategyPair I₁ I₂ O₁ O₂) (env : EnvironmentSequence I₁ I₂),
  (∃ n, ¬ P (branchNode (fun t => (env t).graph) n)) →
  objective.Accepts (fun n => recordContinuationLetter (execution σ env n)))

include rankExact closed recognizes recent bounded small live escape in
theorem numberedGameTest_realizability_iff
    (initial : NumberedSuccessorChoice (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)
    (initialRep : NumberedBoundaryRep M objective P (fun _ => objective.initial) initial.1.1 initial.2
      (boundaryOrigin P ([] : EnvHistory I₁ I₂))) :
    numberedLeaderGameTest M objective rank initial.1 (numberedGameInitialCode objective rank initial) = true ↔
      ∃ σ : StrategyPair I₁ I₂ O₁ O₂, ∀ env,
        objective.Accepts (fun n => recordContinuationLetter (execution σ env n)) := by
  classical
  rw [numberedLeaderGameTest,TreeNonemptiness.nonempty_correct]
  constructor
  · rintro ⟨tree,accepted⟩
    have accepted' := ((numberedLeaderGame M objective rank initial.1
      (numberedGameInitialCode objective rank initial)).acceptsTree_iff_winningTree tree).mp accepted
    obtain ⟨σ,winning⟩ := numberedGame_execution_soundness M objective rank rankExact P closed recognizes recent bounded small
      initial initialRep tree accepted'
    refine ⟨σ,?_⟩
    intro env
    by_cases prefixes : ∀ n, P (branchNode (fun t => (env t).graph) n)
    · exact winning env prefixes
    · exact escape σ env (not_forall.mp prefixes)
  · rintro ⟨σ,winning⟩
    obtain ⟨table,accepted⟩ := numberedGame_complete M objective rank rankExact P closed recognizes recent bounded
      initial initialRep live σ winning
    exact ⟨table.toTransitionRationalTree.labeledTree,
      ((numberedLeaderGame M objective rank initial.1 (numberedGameInitialCode objective rank initial)).acceptsTree_iff_winningTree _).mpr accepted⟩

include rankExact closed recognizes recent bounded small live escape in
theorem numberedGameTest_exists_correct (positive : 0 < B) :
    ∃ initial : NumberedSuccessorChoice (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective,
      NumberedBoundaryRep M objective P (fun _ => objective.initial) initial.1.1 initial.2
        (boundaryOrigin P ([] : EnvHistory I₁ I₂)) ∧
      (numberedLeaderGameTest M objective rank initial.1 (numberedGameInitialCode objective rank initial) = true ↔
        ∃ σ : StrategyPair I₁ I₂ O₁ O₂, ∀ env,
          objective.Accepts (fun n => recordContinuationLetter (execution σ env n))) := by
  obtain ⟨initial,represented⟩ := numberedInitialChoice_exists M objective P positive bounded
  exact ⟨initial,represented,numberedGameTest_realizability_iff M objective rank rankExact P closed recognizes recent bounded small
    live escape initial represented⟩

end
end Characterisation
