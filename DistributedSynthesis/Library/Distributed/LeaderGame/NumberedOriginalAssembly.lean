/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.NumberedOriginalTransition

/-! Assemble the original winning strategy's concrete numbered game tree.
One source and one complete successor family are fixed at each public node;
the existing history-lifting theorem supplies global hidden-thread parity. -/
namespace Characterisation
open DistributedSynthesis

section
variable {GQ I₁ I₂ O₁ O₂ : Type} {d K B C : Nat}
variable [Fintype GQ] [DecidableEq GQ]
variable (M : Recognizer Graph GQ) [DecidablePred (· ∈ M.accept)]
variable (objective : DetParityAutomaton (ContinuationLetter I₁ I₂ O₁ O₂))
variable (rank : objective.State → Fin (C+1)) (P : List Graph → Prop)
variable (σ : StrategyPair I₁ I₂ O₁ O₂)

structure NumberedOriginalSource where
  choice : NumberedSuccessorChoice (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective
  root : EnvHistory I₁ I₂
  live : P (History.graphSequence root)
  boundary : leaderBoundary P d root = true
  represented : NumberedBoundaryRep M objective P
    (strategyHistoryLabel σ (fun s input output => objective.step s (input,output)) objective.initial)
    choice.1.1 choice.2 (boundaryOrigin P root)

def numberedOriginalPast (source : NumberedOriginalSource (d:=d) (K:=K) (B:=B) (C:=C) M objective P σ)
    (i : Fin (B+1)) : EnvHistory I₁ I₂ :=
  if inside : i.val < source.choice.1.1.1.val then source.choice.2 ⟨i.val,inside⟩ else source.root

omit [Fintype GQ] [DecidableEq GQ] [DecidablePred (· ∈ M.accept)] in
theorem numberedOriginalPast_at
    (source : NumberedOriginalSource (d:=d) (K:=K) (B:=B) (C:=C) M objective P σ)
    (i : Fin source.choice.1.1.1.val) :
    numberedOriginalPast M objective P σ source (numberedLeaderSlot objective source.choice.1.1 i) = source.choice.2 i := by
  simp only [numberedOriginalPast,numberedLeaderSlot,dif_pos i.isLt]

omit [Fintype GQ] [DecidableEq GQ] [DecidablePred (· ∈ M.accept)] in
theorem numberedOriginalPast_depth
    (source : NumberedOriginalSource (d:=d) (K:=K) (B:=B) (C:=C) M objective P σ)
    (i : Fin (B+1)) : List.length (numberedOriginalPast M objective P σ source i) = List.length source.root := by
  unfold numberedOriginalPast
  split
  · exact source.represented.2.2.1 _
  · rfl

variable [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
variable [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂]
variable [Inhabited I₁] [Inhabited I₂] [Inhabited O₁] [Inhabited O₂]
variable [DecidableEq objective.State]
variable (closed : PrefixClosed P) (recognizes : ∀ g, P g ↔ M.eval g ∈ M.accept)
variable (recent : ∀ g, P g → ∃ p, RecentOther P d g p)
variable (bounded : ∀ g, P g → Finite (HistoryComponent P g) ∧ Nat.card (HistoryComponent P g) ≤ K)
variable (winning : ∀ env, objective.Accepts (fun n => recordContinuationLetter (execution σ env n)))

include closed recognizes recent bounded winning in
theorem numberedOriginalSource_successors
    (source : NumberedOriginalSource (d:=d) (K:=K) (B:=B) (C:=C) M objective P σ) :
    ∃ move : NumberedLeaderMove (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective,
      numberedLeaderLegal M objective rank source.choice.1.1 move = true ∧
      ∀ outcome, numberedLeaderOffers objective move outcome = true →
        ∃ target : NumberedOriginalSource (d:=d) (K:=K) (B:=B) (C:=C) M objective P σ,
          LeaderSuccessor
            (fun h => (rank (strategyHistoryLabel σ (fun s input output => objective.step s (input,output)) objective.initial h)).val)
            (fun s => s.choice.1) (numberedOriginalPast M objective P σ) (fun s => List.length s.root)
            source outcome target := by
  obtain ⟨e,numbering⟩ := numberedBoundaryRep_enumeration M objective P _ source.choice.1.1 source.choice.2
    source.root source.represented
  have family : (fun i => (e i).val) = source.choice.2 := funext numbering
  have residual : ContinuationWins objective.AcceptsFrom (fun i => (source.choice.1.1.2.2 i).1.2)
      (strategyContinuationPolicy σ (fun i => (e i).val)) := by
    rw [family]
    have labels := funext source.represented.2.2.2.2.2
    rw [labels]
    exact continuationWins_at_histories objective σ winning source.choice.2
  obtain ⟨move,legal,successors⟩ := numberedOriginal_legal_successors M objective rank P closed recognizes recent bounded
    source.choice.1.1 source.root e source.live source.boundary
    (by rw [family]; exact source.represented.2.2.2.1)
    (by intro i; rw [numbering]; exact source.represented.2.2.2.2.1 i) σ residual
  refine ⟨move,legal,?_⟩
  intro outcome offered
  have member : outcome ∈ move.2 := of_decide_eq_true offered
  obtain ⟨root,past,live,phase,rep⟩ := successors outcome member
  rw [family] at rep
  have truth := numberedOriginal_successor_rep M objective rank P σ source.choice.1.1 source.choice.2
    (boundaryOrigin P source.root) (boundaryOrigin P root) source.represented outcome past rep
  let target : NumberedOriginalSource (d:=d) (K:=K) (B:=B) (C:=C) M objective P σ :=
    ⟨⟨outcome,past⟩,root,live,phase.end_boundary,truth.1⟩
  refine ⟨target,rfl,phase.start_lt,?_,?_⟩
  · intro i
    obtain ⟨j,word,parent,extension,_,_⟩ := rep.2.2.2.2.2.2 i
    rw [parent,numberedOriginalPast_at]
    change (source.choice.2 j).IsPrefix
      (numberedOriginalPast M objective P σ target (numberedLeaderSlot objective target.choice.1.1 i))
    rw [numberedOriginalPast_at]
    exact ⟨word,extension.symm⟩
  · intro i
    change (outcome.2.2 i).val = historyPhaseMinimum _ _ _
      (numberedOriginalPast M objective P σ target (numberedLeaderSlot objective target.choice.1.1 i))
    rw [numberedOriginalPast_at]
    exact truth.2 i

include closed recognizes recent bounded winning in
theorem numberedOriginal_finite_game
    (physicalWins : ∀ physical : Nat → RoundRecord I₁ I₂ Graph Unit Unit,
      NatSeqMinEvenParity (fun n => (rank (strategyHistoryLabel σ
        (fun s input output => objective.step s (input,output)) objective.initial (branchNode physical (n+1)))).val))
    (initial : NumberedOriginalSource (d:=d) (K:=K) (B:=B) (C:=C) M objective P σ)
    (zero : initial.root = []) (code : HandoverCode B C) :
    ∃ table : RunParityTreeAutomaton.StateControlledTreeTable
        (numberedLeaderGame M objective rank initial.choice.1 code).toRunAutomaton,
      (numberedLeaderGame M objective rank initial.choice.1 code).WinningTree
        table.toTransitionRationalTree.labeledTree := by
  classical
  letI : Inhabited (NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective) := ⟨initial.choice.1⟩
  let choices := numberedOriginalSource_successors (B:=B) M objective rank P σ closed recognizes recent bounded winning
  let move := fun source => (choices source).choose
  have legal := fun source => (choices source).choose_spec.1
  have successors := fun source outcome offered => (choices source).choose_spec.2 outcome offered
  exact finite_leader_tree_from_successors
    (fun h => (rank (strategyHistoryLabel σ (fun s input output => objective.step s (input,output)) objective.initial h)).val)
    (numberedLeaderOffers objective) (fun s => s.choice.1) (numberedOriginalPast M objective P σ)
    (fun s => List.length s.root) move successors initial (numberedOriginalPast_depth M objective P σ)
    (by simp only [zero,List.length_nil]) (fun header move => numberedLeaderLegal M objective rank header move = true)
    legal physicalWins code

end
end Characterisation
