/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.ActualHandoverOffers
import DistributedSynthesis.Library.Distributed.LeaderGame.NumberedLeaderGame

/-! Every actual rightward phase ending is an advertised outcome of its
accepted numbered table. All target slots belong to one complete certificate;
the witness is not selected independently for the actual hidden slot. -/
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
variable (header : NumberedLeaderHeader (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)
variable (permitted : Finset (NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective))
variable (table : NumberedRightTable M objective rank header permitted)

def rightHandoverNode (h : EnvHistory I₁ I₂) (a : Nat) : List (I₂ × I₁) :=
  (boundaryPhaseWord d h a).map (fun r => (r.inputTwo,r.inputOne))

noncomputable def rightHandoverState (h : EnvHistory I₁ I₂) (a : Nat) :=
  let tree := narrowedInducedTree (numberedRightGuard M objective rank header permitted table.1)
    table.2.toTransitionRationalTree.labeledTree
  let node := rightHandoverNode (d:=d) h a
  numberedPhaseRun M objective rank header table.1 (receiverOfTree tree) (senderOfTree tree)
    (fun i => node.getD i default) node.length

variable (P : List Graph → Prop) (closed : PrefixClosed P)
variable (recognizes : ∀ g, P g ↔ M.eval g ∈ M.accept)
variable (recent : ∀ g, P g → ∃ p, RecentOther P d g p)
variable (bounded : ∀ g, P g → Finite (HistoryComponent P g) ∧ Nat.card (HistoryComponent P g) ≤ K)
variable (small : ∀ k : EnvHistory I₁ I₂, P (History.graphSequence k) → leaderBoundary P d k = true →
  Nat.card (InputHistoryComponent P k) ≤ B)

include closed recognizes recent bounded small in
theorem numberedRightTable_actual_handover
    (winning : NarrowedAllThreadsWin (numberedRightGuard M objective rank header permitted table.1)
      table.2.toTransitionRationalTree.labeledTree)
    (h : EnvHistory I₁ I₂) (live : P (History.graphSequence h)) (a : Nat)
    (phase : ConsecutiveLeaderBoundaries P d h a)
    (e : Fin header.1.val ≃ InputHistoryComponent P (h.take a))
    (shape : RepresentsInputShape (fun i => (e i).val) header.2.1)
    (graphs : ∀ i, GraphRootRep P M (History.graphSequence (e i).val) (header.2.2 i).1.1)
    (leader : componentLeader P d (History.graphSequence (h.take a)) = .one) :
    let state := rightHandoverState M objective rank header permitted table h a
    let past := boundaryPhaseSources P d h a ∘ e
    ∃ (n : Fin (d+1)) (root : ClosingLayer (ActiveClosingRoots state.1.2.1) I₁ I₂ (n.val+1))
      (move : ClosingBoundaryCertificate (ActiveClosingRoots state.1.2.1) I₁ I₂ O₁ O₂
        (LeaderAnnotation (GQ:=GQ) (d:=d) (K:=K) (C:=C) objective) B (d+1) (n.val+1)),
      n.val+1 = List.length h-phaseClosingCut d h a ∧
      closingLayerHistory (past ∘ Subtype.val) (n.val+1) root = h ∧
      ClosingOfferRealizes P (past ∘ Subtype.val) (leaderAnnotationStep M objective rank)
        (state.1.2.2 ∘ Subtype.val) (restrictClosingPolicy Subtype.val (closingPolicyOfBank state.2.1))
        (by omega) root move ∧
      certificateHandover (numberedLeaderSlot objective header ∘ Subtype.val) (fun q => q.2 ()) move ∈ permitted := by
  let guard := numberedRightGuard M objective rank header permitted table.1
  let tree := narrowedInducedTree guard table.2.toTransitionRationalTree.labeledTree
  let receiver := receiverOfTree tree
  let sender := senderOfTree tree
  let node := rightHandoverNode (d:=d) h a
  let env := fun i => node.getD i default
  let state := rightHandoverState M objective rank header permitted table h a
  let past := fun i => (e i).val
  have branch : branchNode env node.length = node := by
    simpa only [List.take_length] using rollingBranch_take node node.length le_rfl
  have bounds := phaseClosingCut_bounds P d h a phase
  have depth : ∀ i, List.length (past i) = a := by
    intro i
    have len := (inputConnected_length P (e i).property).symm
    simpa only [List.length_take,min_eq_left (Nat.le_of_lt phase.start_lt)] using len
  have sources : boundaryPhaseSources P d h a ∘ e = rollingSourceHistory past node := by
    rw [boundaryPhaseSources_as_rolling P d h a phase leader]
    rfl
  have length : a + node.length = phaseClosingCut d h a := by
    simp only [node,rightHandoverNode,List.length_map,boundaryPhaseWord,List.length_drop,
      List.length_take,min_eq_left (Nat.le_of_lt bounds.2.1)]
    omega
  have current := jointGraphLeaderMemory_rolling_sources M P closed recognizes bounded past a depth
    (fun i => (header.2.2 i).1.1) graphs (leaderAnnotationStep M objective rank)
    (fun i => resetLeaderMinimum objective (header.2.2 i)) (shapeLeaderGroup header.2.1 .one)
    table.1 receiver sender env node.length
  rw [branch] at current
  have flag : state.2.2 = decide (node.length = 0) := current.2.2.2
  have currentShape := jointLeaderShape_exact past header.2.1 shape node
  have empty : (node = []) ↔ node.length = 0 := List.length_eq_zero_iff.symm
  simp only [empty] at currentShape
  have represented : RepresentsInputShape (boundaryPhaseSources P d h a ∘ e)
      (jointLeaderShape header.2.1 state.2.2) := by
    rw [sources,flag]
    exact currentShape
  obtain ⟨σ,plans,_,_⟩ := numberedRightTable_readback M objective rank header permitted table winning past shape a depth
  have coherent : ClosingPolicyCoherent (jointLeaderShape header.2.1 state.2.2) (closingPolicyOfBank state.2.1) := by
    have truth := closingBankOfStrategy_coherent (D:=d) σ (rollingSourceHistory past node)
      (jointLeaderShape header.2.1 (decide (node.length = 0))) currentShape
    have banks : (fun i => closingPlanOfStrategy σ (rollingSourceHistory past node i) (d+1)) = state.2.1 := by
      funext i
      exact (plans node i).trans (congrFun current.2.2.1 i).symm
    rw [banks] at truth
    rw [flag]
    exact truth
  have active : SourceActivityOnLive P d a (phaseClosingCut d h a)
      (boundaryPhaseSources P d h a ∘ e) state.1.2.1 := by
    rw [sources,← length]
    exact current.2.1
  have representedGraphs : ∀ i, GraphRootRep P M
      (History.graphSequence ((boundaryPhaseSources P d h a ∘ e) i)) (state.1.1 i) := by
    rw [sources]
    exact current.1
  obtain ⟨n,root,move,age,actual,_,realizes,offered⟩ := numbered_actual_handover_offer M P closed recognizes d recent
    h live a phase e (jointLeaderShape header.2.1 state.2.2) represented state.1.2.1 active state.1.1
    representedGraphs bounded small (leaderAnnotationStep M objective rank) state.1.2.2
    (closingPolicyOfBank state.2.1) coherent (numberedLeaderSlot objective header) (fun q => q.2 ())
  have guarded : guard.WinsPlay (pairPlay receiver sender env) := by
    rw [pairPlay,treeOfPair_ofTree (senderOblivious_narrowedInducedTree guard _)]
    exact (guard.lift_winningTree_iff tree).mp (narrowedInducedTree_winningTree_of_allThreadsWin guard winning) env
  have subset := ((phaseOfferMonitor_wins_iff _ _ _ _ _ _ _).mp guarded).2 node.length
  have initial : state.2.2 = decide (List.length (boundaryPhaseWord d h a) = 0) := by
    rw [flag]
    simp only [node,rightHandoverNode,List.length_map]
  have member : certificateHandover (numberedLeaderSlot objective header ∘ Subtype.val) (fun q => q.2 ()) move ∈
      jointGraphLeaderCollect M (leaderAnnotationStep M objective rank) header.2.1
        (numberedLeaderSlot objective header) (fun q => q.2 ()) state (pairPlay receiver sender env node.length) := by
    change _ ∈ graphClosingOffers M state.1.1 state.1.2.1 (jointLeaderShape header.2.1 state.2.2)
      state.2.2 (leaderAnnotationStep M objective rank) state.1.2.2 (closingPolicyOfBank state.2.1) _ _
    rw [initial]
    rw [initial] at offered
    exact offered
  exact ⟨n,root,move,age,actual,realizes,subset member⟩

end
end Characterisation
