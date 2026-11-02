/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.NumberedOriginalReplay

/-! Every offered outcome of an original winning continuation has one live
successor family, with exact histories, annotations, and predecessor links.
The family is selected before any hidden slot is followed. -/
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
variable (P : List Graph → Prop) (closed : PrefixClosed P)
variable (recognizes : ∀ g, P g ↔ M.eval g ∈ M.accept)
variable (recent : ∀ g, P g → ∃ p, RecentOther P d g p)
variable (bounded : ∀ g, P g → Finite (HistoryComponent P g) ∧ Nat.card (HistoryComponent P g) ≤ K)
variable (header : NumberedLeaderHeader (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)
variable (u : EnvHistory I₁ I₂) (e : Fin header.1.val ≃ InputHistoryComponent P u)
variable (liveU : P (History.graphSequence u)) (startU : leaderBoundary P d u = true)
variable (shape : RepresentsInputShape (fun i => (e i).val) header.2.1)
variable (graphs : ∀ i, GraphRootRep P M (History.graphSequence (e i).val) (header.2.2 i).1.1)
variable (σ : StrategyPair I₁ I₂ O₁ O₂)
variable (winning : ContinuationWins objective.AcceptsFrom (fun i => (header.2.2 i).1.2)
  (strategyContinuationPolicy σ (fun i => (e i).val)))

include closed recognizes recent bounded liveU startU shape graphs winning in
theorem numberedOriginal_right_successors :
    ∃ permitted, numberedRightLegal M objective rank header permitted = true ∧
      ∀ outcome, outcome ∈ permitted → ∃ target nextPast,
        P (History.graphSequence target) ∧
        ConsecutiveLeaderBoundaries P d target (List.length u) ∧
        NumberedSuccessorRep M objective rank P header (fun i => (e i).val) σ
          (boundaryOrigin P target) outcome nextPast := by
  obtain ⟨base,_,same,permitted,legal,witnesses⟩ := numbered_right_with_complete_successors
    M objective rank header P closed recognizes recent bounded u e liveU startU shape graphs σ winning
  have readback := originalRight_readback d σ (fun i => (e i).val)
    (shapeLeaderGroup header.2.1 .one) base same
  refine ⟨permitted,legal,?_⟩
  intro outcome member
  obtain ⟨env,n,t,root,move,rfl,realizes,liveRoot,phases⟩ := witnesses outcome member
  have labels := numberedRight_handover_labels M objective rank header P (fun i => (e i).val) σ
    (rollingOriginalBank σ (fun i => (e i).val) d [])
    (rollingOriginalReceiver σ (fun i => (e i).val) d)
    (jointOriginalLeader σ base) readback.1 readback.2 env n (t.val+1) (by omega) root move realizes
  let state := numberedPhaseRun M objective rank header
    (rollingOriginalBank σ (fun i => (e i).val) d [])
    (rollingOriginalReceiver σ (fun i => (e i).val) d) (jointOriginalLeader σ base) env n
  let past : ActiveClosingRoots state.1.2.1 → EnvHistory I₁ I₂ := rollingSourceHistory (fun i => (e i).val) (branchNode env n) ∘ Subtype.val
  let target := closingLayerHistory past (t.val+1) root
  have rootPhase : ConsecutiveLeaderBoundaries P d target (List.length u) := by
    obtain ⟨i,equal⟩ := (realizes.2.1 target).mp Relation.ReflTransGen.refl
    rw [← equal]
    exact phases i
  refine ⟨target,closingLayerHistory past (t.val+1) ∘ move.2.2.1,liveRoot,rootPhase,?_⟩
  exact numberedCertificate_successor M objective rank P header (fun i => (e i).val) σ
    closed recognizes bounded graphs Subtype.val (rightInputHistory (branchNode env n)) _ _
    (t.val+1) (by omega) (by omega) root move realizes labels

include closed recognizes recent bounded liveU startU shape graphs winning in
theorem numberedOriginal_left_successors :
    ∃ permitted, numberedLeftLegal M objective rank header permitted = true ∧
      ∀ outcome, outcome ∈ permitted → ∃ target nextPast,
        P (History.graphSequence target) ∧
        ConsecutiveLeaderBoundaries P d target (List.length u) ∧
        NumberedSuccessorRep M objective rank P header (fun i => (e i).val) σ
          (boundaryOrigin P target) outcome nextPast := by
  obtain ⟨base,_,same,permitted,legal,witnesses⟩ := numbered_left_with_complete_successors
    M objective rank header P closed recognizes recent bounded u e liveU startU shape graphs σ winning
  have readback := originalLeft_readback d σ (fun i => (e i).val)
    (shapeLeaderGroup header.2.1 .two) base same
  refine ⟨permitted,legal,?_⟩
  intro outcome member
  obtain ⟨env,n,t,root,move,rfl,realizes,liveRoot,phases⟩ := witnesses outcome member
  have labels := numberedLeft_handover_labels M objective rank header P (fun i => (e i).val) σ
    (rollingOriginalBank (exchangeStrategy σ) (exchangeHistory ∘ fun i => (e i).val) d [])
    (rollingOriginalReceiver (exchangeStrategy σ) (exchangeHistory ∘ fun i => (e i).val) d)
    (jointOriginalLeader (exchangeStrategy σ) base) readback.1 readback.2 env n (t.val+1) (by omega) root move realizes
  let state := numberedLeftPhaseRun M objective rank header
    (rollingOriginalBank (exchangeStrategy σ) (exchangeHistory ∘ fun i => (e i).val) d [])
    (rollingOriginalReceiver (exchangeStrategy σ) (exchangeHistory ∘ fun i => (e i).val) d)
    (jointOriginalLeader (exchangeStrategy σ) base) env n
  let past : ActiveClosingRoots state.1.2.1 → EnvHistory I₁ I₂ := leftSourceHistory (fun i => (e i).val) (branchNode env n) ∘ Subtype.val
  let target := closingLayerHistory past (t.val+1) root
  have rootPhase : ConsecutiveLeaderBoundaries P d target (List.length u) := by
    obtain ⟨i,equal⟩ := (realizes.2.1 target).mp Relation.ReflTransGen.refl
    rw [← equal]
    exact phases i
  refine ⟨target,closingLayerHistory past (t.val+1) ∘ move.2.2.1,liveRoot,rootPhase,?_⟩
  exact numberedCertificate_successor M objective rank P header (fun i => (e i).val) σ
    closed recognizes bounded graphs Subtype.val (leftInputHistory (branchNode env n)) _ _
    (t.val+1) (by omega) (by omega) root move realizes labels

include closed recognizes recent bounded liveU startU shape graphs winning in
theorem numberedOriginal_legal_successors :
    ∃ move : NumberedLeaderMove (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective,
      numberedLeaderLegal M objective rank header move = true ∧
      ∀ outcome, outcome ∈ move.2 → ∃ target nextPast,
        P (History.graphSequence target) ∧
        ConsecutiveLeaderBoundaries P d target (List.length u) ∧
        NumberedSuccessorRep M objective rank P header (fun i => (e i).val) σ
          (boundaryOrigin P target) outcome nextPast := by
  have leaders : ∀ h, graphRootLeader (header.2.2 h).1.1 = componentLeader P d (History.graphSequence u) := by
    intro h
    rw [graphRootLeader_exact P M _ (inputConnected_live P liveU (e h).property) _ (graphs h)]
    exact (componentLeader_component_invariant P d (inputConnected_projects P (e h).property)).symm
  cases direction : componentLeader P d (History.graphSequence u) with
  | one =>
    obtain ⟨permitted,legal,successors⟩ := numberedOriginal_right_successors M objective rank P closed recognizes recent
      bounded header u e liveU startU shape graphs σ winning
    refine ⟨(.one,permitted),?_,successors⟩
    have agree : ∀ h, graphRootLeader (header.2.2 h).1.1 = .one := fun h => (leaders h).trans direction
    simpa only [numberedLeaderLegal,agree,implies_true,decide_true,Bool.true_and] using legal
  | two =>
    obtain ⟨permitted,legal,successors⟩ := numberedOriginal_left_successors M objective rank P closed recognizes recent
      bounded header u e liveU startU shape graphs σ winning
    refine ⟨(.two,permitted),?_,successors⟩
    have agree : ∀ h, graphRootLeader (header.2.2 h).1.1 = .two := fun h => (leaders h).trans direction
    simpa only [numberedLeaderLegal,agree,implies_true,decide_true,Bool.true_and] using legal

end
end Characterisation
