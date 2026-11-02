/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.NumberedSuccessorSelection

/-! Accepted numbered tables supply the concrete successor selector at every
actual handover. The same fixed readback strategy determines all retained
labels and every compatible target history. -/
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
variable (small : ∀ k : EnvHistory I₁ I₂, P (History.graphSequence k) → leaderBoundary P d k = true →
  Nat.card (InputHistoryComponent P k) ≤ B)
variable (header : NumberedLeaderHeader (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)
variable (permitted : Finset (NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective))

include closed recognizes recent bounded small in
theorem numberedRightTable_actual_successor
    (table : NumberedRightTable M objective rank header permitted)
    (winning : NarrowedAllThreadsWin (numberedRightGuard M objective rank header permitted table.1)
      table.2.toTransitionRationalTree.labeledTree)
    (h : EnvHistory I₁ I₂) (live : P (History.graphSequence h)) (a : Nat)
    (phase : ConsecutiveLeaderBoundaries P d h a)
    (e : Fin header.1.val ≃ InputHistoryComponent P (h.take a))
    (shape : RepresentsInputShape (fun i => (e i).val) header.2.1)
    (graphs : ∀ i, GraphRootRep P M (History.graphSequence (e i).val) (header.2.2 i).1.1)
    (selected : componentLeader P d (History.graphSequence (h.take a)) = .one)
    (σ : StrategyPair I₁ I₂ O₁ O₂) :
    let tree := narrowedInducedTree (numberedRightGuard M objective rank header permitted table.1)
      table.2.toTransitionRationalTree.labeledTree
    let receiver := receiverOfTree tree
    let leader := senderOfTree tree
    let past := fun i => (e i).val
    (∀ node i, closingPlanOfStrategy σ (rollingSourceHistory past node i) (d+1) =
      receiverClosingBank table.1 receiver node i) →
    (∀ node r i,
      σ.one (currentView .one (rollingSourceHistory past (node++[r]) i)) =
        leader (senderWord node) r.2 (shapeLeaderGroup header.2.1 .one i) ∧
      σ.two (currentView .two (rollingSourceHistory past (node++[r]) i)) = (receiver node r).1 i) →
    ∃ outcome nextPast, outcome ∈ permitted ∧
      NumberedSuccessorRep M objective rank P header past σ (boundaryOrigin P h) outcome nextPast := by
  dsimp only
  intro plans outputs
  let tree := narrowedInducedTree (numberedRightGuard M objective rank header permitted table.1)
    table.2.toTransitionRationalTree.labeledTree
  let receiver := receiverOfTree tree
  let leader := senderOfTree tree
  let past := fun i => (e i).val
  let node := rightHandoverNode (d:=d) h a
  let env := fun i => node.getD i default
  let state := rightHandoverState M objective rank header permitted table h a
  have branch : branchNode env node.length = node := by
    simpa only [List.take_length] using rollingBranch_take node node.length le_rfl
  have sources : boundaryPhaseSources P d h a ∘ e = rollingSourceHistory past (branchNode env node.length) := by
    rw [branch,boundaryPhaseSources_as_rolling P d h a phase selected]
    rfl
  obtain ⟨n,root,move,_,actual,realizes,offered⟩ := numberedRightTable_actual_handover
    M objective rank header permitted table P closed recognizes recent bounded small
    winning h live a phase e shape graphs selected
  have realization : ClosingOfferRealizes P (rollingSourceHistory past (branchNode env node.length) ∘ Subtype.val)
      (leaderAnnotationStep M objective rank) (state.1.2.2 ∘ Subtype.val)
      (restrictClosingPolicy Subtype.val (closingPolicyOfBank state.2.1)) (by omega) root move := by
    rw [← sources]
    exact realizes
  have labels := numberedRight_handover_labels M objective rank header P past σ table.1 receiver leader
    plans outputs env node.length (n.val+1) (by omega) root move realization
  have rep := numberedCertificate_successor M objective rank P header past σ closed recognizes bounded graphs
    (Subtype.val : ActiveClosingRoots state.1.2.1 → Fin header.1.val)
    (rightInputHistory (branchNode env node.length)) (state.1.2.2 ∘ Subtype.val)
    (restrictClosingPolicy Subtype.val (closingPolicyOfBank state.2.1))
    (n.val+1) (by omega) (by omega) root move realization labels
  change NumberedSuccessorRep M objective rank P header past σ
    (boundaryOrigin P (closingLayerHistory (rollingSourceHistory past (branchNode env node.length) ∘ Subtype.val)
      (n.val+1) root))
    (certificateHandover (numberedLeaderSlot objective header ∘ Subtype.val) (fun q => q.2 ()) move)
    (closingLayerHistory (rollingSourceHistory past (branchNode env node.length) ∘ Subtype.val)
      (n.val+1) ∘ move.2.2.1) at rep
  rw [← sources,actual] at rep
  exact ⟨_,_,offered,rep⟩

include closed recognizes recent bounded small in
theorem numberedLeftTable_actual_successor
    (table : NumberedLeftTable M objective rank header permitted)
    (winning : NarrowedAllThreadsWin (numberedLeftGuard M objective rank header permitted table.1)
      table.2.toTransitionRationalTree.labeledTree)
    (h : EnvHistory I₁ I₂) (live : P (History.graphSequence h)) (a : Nat)
    (phase : ConsecutiveLeaderBoundaries P d h a)
    (e : Fin header.1.val ≃ InputHistoryComponent P (h.take a))
    (shape : RepresentsInputShape (fun i => (e i).val) header.2.1)
    (graphs : ∀ i, GraphRootRep P M (History.graphSequence (e i).val) (header.2.2 i).1.1)
    (selected : componentLeader P d (History.graphSequence (h.take a)) = .two)
    (σ : StrategyPair I₁ I₂ O₁ O₂) :
    let tree := narrowedInducedTree (numberedLeftGuard M objective rank header permitted table.1)
      table.2.toTransitionRationalTree.labeledTree
    let receiver := receiverOfTree tree
    let leader := senderOfTree tree
    let past := fun i => (e i).val
    (∀ node i, closingPlanOfStrategy σ (leftSourceHistory past node i) (d+1) =
      exchangePlan (receiverClosingBank table.1 receiver node i)) →
    (∀ node r i,
      σ.one (currentView .one (leftSourceHistory past (node++[r]) i)) = (receiver node r).1 i ∧
      σ.two (currentView .two (leftSourceHistory past (node++[r]) i)) =
        leader (senderWord node) r.2 (shapeLeaderGroup header.2.1 .two i)) →
    ∃ outcome nextPast, outcome ∈ permitted ∧
      NumberedSuccessorRep M objective rank P header past σ (boundaryOrigin P h) outcome nextPast := by
  dsimp only
  intro plans outputs
  let tree := narrowedInducedTree (numberedLeftGuard M objective rank header permitted table.1)
    table.2.toTransitionRationalTree.labeledTree
  let receiver := receiverOfTree tree
  let leader := senderOfTree tree
  let past := fun i => (e i).val
  let node := leftHandoverNode (d:=d) h a
  let env := fun i => node.getD i default
  let state := leftHandoverState M objective rank header permitted table h a
  have branch : branchNode env node.length = node := by
    simpa only [List.take_length] using rollingBranch_take node node.length le_rfl
  have sources : boundaryPhaseSources P d h a ∘ e = leftSourceHistory past (branchNode env node.length) := by
    rw [branch,boundaryPhaseSources_as_left P d h a phase selected]
    rfl
  obtain ⟨n,root,move,_,actual,realizes,offered⟩ := numberedLeftTable_actual_handover
    M objective rank header permitted table P closed recognizes recent bounded small
    winning h live a phase e shape graphs selected
  have realization : ClosingOfferRealizes P (leftSourceHistory past (branchNode env node.length) ∘ Subtype.val)
      (leaderAnnotationStep M objective rank) (state.1.2.2 ∘ Subtype.val)
      (restrictClosingPolicy Subtype.val (closingPolicyOfBank (fun i => exchangePlan (state.2.1 i))))
      (by omega) root move := by
    rw [← sources]
    exact realizes
  have labels := numberedLeft_handover_labels M objective rank header P past σ table.1 receiver leader
    plans outputs env node.length (n.val+1) (by omega) root move realization
  have rep := numberedCertificate_successor M objective rank P header past σ closed recognizes bounded graphs
    (Subtype.val : ActiveClosingRoots state.1.2.1 → Fin header.1.val)
    (leftInputHistory (branchNode env node.length)) (state.1.2.2 ∘ Subtype.val)
    (restrictClosingPolicy Subtype.val (closingPolicyOfBank (fun i => exchangePlan (state.2.1 i))))
    (n.val+1) (by omega) (by omega) root move realization labels
  change NumberedSuccessorRep M objective rank P header past σ
    (boundaryOrigin P (closingLayerHistory (leftSourceHistory past (branchNode env node.length) ∘ Subtype.val)
      (n.val+1) root))
    (certificateHandover (numberedLeaderSlot objective header ∘ Subtype.val) (fun q => q.2 ()) move)
    (closingLayerHistory (leftSourceHistory past (branchNode env node.length) ∘ Subtype.val)
      (n.val+1) ∘ move.2.2.1) at rep
  rw [← sources,actual] at rep
  exact ⟨_,_,offered,rep⟩

end
end Characterisation
