/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.NumberedEndlessPhase

/-! A winning tree of the concrete numbered game yields one physical
distributed strategy. Infinite handovers and a final endless leader phase
are handled by that same strategy and the same carried state assignment. -/
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
variable (initial : NumberedSuccessorChoice (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)

include rankExact closed recognizes recent bounded small in
theorem numberedGame_winning_strategy
    (initialRep : NumberedBoundaryRep M objective P (fun _ => objective.initial) initial.1.1 initial.2
      (boundaryOrigin P ([] : EnvHistory I₁ I₂)))
    (tree : LabeledTree
      (NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)
      (NumberedLeaderMove (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective))
    (accepted : (numberedLeaderGame M objective rank initial.1 (numberedGameInitialCode objective rank initial)).WinningTree tree) :
    ∃ σ : StrategyPair I₁ I₂ O₁ O₂,
      ∀ (history : Nat → EnvHistory I₁ I₂)
        (_depth : ∀ n, List.length (history n) = n)
        (_prefixes : ∀ m n, m ≤ n → (history n).take m = history m)
        (_live : ∀ n, P (History.graphSequence (history n)))
        (round : Nat → RoundRecord I₁ I₂ Graph Unit Unit)
        (_next : ∀ n, history (n+1) = history n ++ [round n]),
        NatSeqMinEvenParity (fun n => objective.priority (strategyHistoryLabel σ
          (fun s input output => objective.step s (input,output)) objective.initial (history (n+1)))) := by
  classical
  letI : Inhabited (NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective) := ⟨initial.1⟩
  obtain ⟨read,σ,reads,impl,labels,infiniteWins⟩ := numberedGame_infinite_handover_soundness M objective rank P tree initial
    closed recognizes recent bounded small initialRep accepted
  have accepted' : (supportedLeaderProgressMonitor (numberedLeaderOffers objective)
      (numberedGameInitialCode objective rank initial) initial.1
      (fun header move => numberedLeaderLegal M objective rank header move = true)).WinningTree tree := accepted
  have validTree := ((supportedLeaderProgress_winning_iff (numberedLeaderOffers objective)
    (numberedGameInitialCode objective rank initial) initial.1
    (fun header move => numberedLeaderLegal M objective rank header move = true) tree).mp accepted').1
  refine ⟨σ,?_⟩
  intro history depth prefixes live round next
  by_cases infinite : InfinitelyManyLeaderBoundaries P d history
  · obtain ⟨cuts,phases⟩ := exists_leader_phase_cuts P d history infinite
    simpa only [rankExact] using infiniteWins history depth prefixes live cuts phases
  · obtain ⟨N,start,absent⟩ := finite_boundaries_last_phase P d history depth prefixes infinite
    let machine := numberedGameMachine M objective rank P tree initial
    let state := machine (history N)
    let origin := boundaryOrigin P (history N)
    let controllers := fun origin => numberedGameDecode M objective rank tree origin (read origin)
    have boundary : leaderBoundary P d (history N) = true := by
      rcases start with zero | boundary
      · have empty : history N = [] := List.eq_nil_of_length_eq_zero (by rw [depth,zero])
        rw [empty]
        exact leaderBoundary_empty P d
      · exact boundary
    have valid := numberedGameMachine_valid M objective rank P tree initial closed recognizes recent bounded small
      validTree initialRep (history N) (live N) boundary
    have legal := validTree state.data.1 valid.1
    rw [← valid.2.1] at legal
    have tail := numberedController_final_accepts M objective rank P state.label state.data.2.1.1 state.data.2.2
      (tree state.data.1) history round next N (live N) absent valid.2.2 legal
    have label := labels (history N) (live N)
    change state.label (history N) = _ at label
    rw [label] at tail
    let env := fun n => ((round (N+n)).inputOne,(round (N+n)).inputTwo,(round (N+n)).graph)
    have continuation : ∀ n, history N ++
        (branchNode env n).map (fun r => (⟨r.1,r.2.1,r.2.2,(),()⟩ : RoundRecord I₁ I₂ Graph Unit Unit)) = history (N+n) := by
      intro n
      induction n with
      | zero => simp only [branchNode,List.map_nil,List.append_nil,Nat.add_zero]
      | succ n ih =>
        rw [branchNode,List.map_append,List.map_singleton,← List.append_assoc,ih]
        rw [show N+(n+1) = (N+n)+1 by omega,next]
    have acceptedTail : objective.AcceptsFrom
        (strategyHistoryLabel σ (fun s input output => objective.step s (input,output)) objective.initial (history N))
        (continuationTrace (strategyContinuationPolicy (controllers origin) (fun _ : Unit => history N)) () env) := by
      dsimp only [controllers,origin]
      rw [reads _ (live N)]
      exact tail
    exact finalPhase_parity_of_accepts P closed d controllers σ impl objective history depth prefixes live
      N start absent env continuation acceptedTail

end
end Characterisation
