/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.ActualHandoverOffers
import DistributedSynthesis.Library.Distributed.LeaderGame.NumberedLeaderGame

/-! Actual leftward handovers satisfy the same original graph collector
and whole-outcome restriction. Only local sender/receiver roles are exchanged. -/
namespace Characterisation
open DistributedSynthesis

theorem outgoing_history_as_left {I₁ I₂ : Type} (h : EnvHistory I₁ I₂)
    (outgoing : ∀ r ∈ h, r.graph = .left) :
    leftInputHistory (h.map (fun r => (r.inputOne,r.inputTwo))) = h := by
  apply Function.LeftInverse.injective exchangeHistory_twice
  have outgoing' : ∀ r ∈ exchangeHistory h, r.graph = .right := by
    intro r member
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp member
    simp only [exchangeRound,outgoing s hs,exchangeGraph]
  have rightward := outgoing_history_as_right (exchangeHistory h) outgoing'
  simpa only [exchangeHistory,leftInputHistory,rightInputHistory,List.map_map,Function.comp_def,exchangeRound,exchangeGraph]
    using rightward

theorem boundaryPhaseSources_as_left {I₁ I₂ : Type}
    (P : List Graph → Prop) (d : Nat) (h : EnvHistory I₁ I₂) (a : Nat)
    (phase : ConsecutiveLeaderBoundaries P d h a)
    (leader : componentLeader P d (History.graphSequence (h.take a)) = .two) :
    boundaryPhaseSources P d h a = leftSourceHistory
      (fun s : InputHistoryComponent P (h.take a) => s.val)
      ((boundaryPhaseWord d h a).map (fun r => (r.inputOne,r.inputTwo))) := by
  have outgoing : ∀ r ∈ boundaryPhaseWord d h a, r.graph = .left := by
    intro r member
    simpa only [leader,leaderOutgoingGraph] using boundaryPhaseWord_outgoing P d h a phase r member
  funext s
  simp only [boundaryPhaseSources,leftSourceHistory,outgoing_history_as_left _ outgoing]

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
variable (table : NumberedLeftTable M objective rank header permitted)

def leftHandoverNode (h : EnvHistory I₁ I₂) (a : Nat) : List (I₁ × I₂) :=
  (boundaryPhaseWord d h a).map (fun r => (r.inputOne,r.inputTwo))

noncomputable def leftHandoverState (h : EnvHistory I₁ I₂) (a : Nat) :=
  let tree := narrowedInducedTree (numberedLeftGuard M objective rank header permitted table.1)
    table.2.toTransitionRationalTree.labeledTree
  let node := leftHandoverNode (d:=d) h a
  numberedLeftPhaseRun M objective rank header table.1 (receiverOfTree tree) (senderOfTree tree)
    (fun i => node.getD i default) node.length

variable (P : List Graph → Prop) (closed : PrefixClosed P)
variable (recognizes : ∀ g, P g ↔ M.eval g ∈ M.accept)
variable (recent : ∀ g, P g → ∃ p, RecentOther P d g p)
variable (bounded : ∀ g, P g → Finite (HistoryComponent P g) ∧ Nat.card (HistoryComponent P g) ≤ K)
variable (small : ∀ k : EnvHistory I₁ I₂, P (History.graphSequence k) → leaderBoundary P d k = true →
  Nat.card (InputHistoryComponent P k) ≤ B)

include closed recognizes recent bounded small in
theorem numberedLeftTable_actual_handover
    (winning : NarrowedAllThreadsWin (numberedLeftGuard M objective rank header permitted table.1)
      table.2.toTransitionRationalTree.labeledTree)
    (h : EnvHistory I₁ I₂) (live : P (History.graphSequence h)) (a : Nat)
    (phase : ConsecutiveLeaderBoundaries P d h a)
    (e : Fin header.1.val ≃ InputHistoryComponent P (h.take a))
    (shape : RepresentsInputShape (fun i => (e i).val) header.2.1)
    (graphs : ∀ i, GraphRootRep P M (History.graphSequence (e i).val) (header.2.2 i).1.1)
    (leader : componentLeader P d (History.graphSequence (h.take a)) = .two) :
    let state := leftHandoverState M objective rank header permitted table h a
    let past := boundaryPhaseSources P d h a ∘ e
    let policy := closingPolicyOfBank (fun i => exchangePlan (state.2.1 i))
    ∃ (n : Fin (d+1)) (root : ClosingLayer (ActiveClosingRoots state.1.2.1) I₁ I₂ (n.val+1))
      (move : ClosingBoundaryCertificate (ActiveClosingRoots state.1.2.1) I₁ I₂ O₁ O₂
        (LeaderAnnotation (GQ:=GQ) (d:=d) (K:=K) (C:=C) objective) B (d+1) (n.val+1)),
      n.val+1 = List.length h-phaseClosingCut d h a ∧
      closingLayerHistory (past ∘ Subtype.val) (n.val+1) root = h ∧
      ClosingOfferRealizes P (past ∘ Subtype.val) (leaderAnnotationStep M objective rank)
        (state.1.2.2 ∘ Subtype.val) (restrictClosingPolicy Subtype.val policy) (by omega) root move ∧
      certificateHandover (numberedLeaderSlot objective header ∘ Subtype.val) (fun q => q.2 ()) move ∈ permitted := by
  let guard := numberedLeftGuard M objective rank header permitted table.1
  let tree := narrowedInducedTree guard table.2.toTransitionRationalTree.labeledTree
  let receiver := receiverOfTree tree
  let sender := senderOfTree tree
  let node := leftHandoverNode (d:=d) h a
  let env := fun i => node.getD i default
  let state := leftHandoverState M objective rank header permitted table h a
  let past := fun i => (e i).val
  let nowShape := exchangeShape (jointLeaderShape (exchangeShape header.2.1) state.2.2)
  let bank := fun i => exchangePlan (state.2.1 i)
  have branch : branchNode env node.length = node := by
    simpa only [List.take_length] using rollingBranch_take node node.length le_rfl
  have bounds := phaseClosingCut_bounds P d h a phase
  have depth : ∀ i, List.length (past i) = a := by
    intro i
    simpa only [List.length_take,min_eq_left (Nat.le_of_lt phase.start_lt)] using
      (inputConnected_length P (e i).property).symm
  have sources : boundaryPhaseSources P d h a ∘ e = leftSourceHistory past node := by
    rw [boundaryPhaseSources_as_left P d h a phase leader]
    rfl
  have length : a + node.length = phaseClosingCut d h a := by
    simp only [node,leftHandoverNode,List.length_map,boundaryPhaseWord,List.length_drop,
      List.length_take,min_eq_left (Nat.le_of_lt bounds.2.1)]
    omega
  have current := numberedLeftPhaseRun_sources M objective rank header table.1 receiver sender env
    P closed recognizes bounded past a depth graphs node.length
  rw [branch] at current
  have flag : state.2.2 = decide (node.length = 0) := current.2.2.2
  have currentShape := leftLeaderShape_exact past header.2.1 shape node
  have empty : (node = []) ↔ node.length = 0 := List.length_eq_zero_iff.symm
  simp only [empty] at currentShape
  have represented : RepresentsInputShape (boundaryPhaseSources P d h a ∘ e) nowShape := by
    rw [sources]
    simpa only [nowShape,flag] using currentShape
  obtain ⟨σ,plans,_,_⟩ := numberedLeftTable_readback M objective rank header permitted table winning past shape a depth
  have coherent : ClosingPolicyCoherent nowShape (closingPolicyOfBank bank) := by
    have truth := closingBankOfStrategy_coherent (D:=d) σ (leftSourceHistory past node) nowShape
      (by rwa [sources] at represented)
    have banks : (fun i => closingPlanOfStrategy σ (leftSourceHistory past node i) (d+1)) = bank := by
      funext i
      exact (plans node i).trans (congrArg exchangePlan (congrFun current.2.2.1 i)).symm
    rw [banks] at truth
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
    h live a phase e nowShape represented state.1.2.1 active state.1.1 representedGraphs bounded small
    (leaderAnnotationStep M objective rank) state.1.2.2 (closingPolicyOfBank bank) coherent
    (numberedLeaderSlot objective header) (fun q => q.2 ())
  have guarded : guard.WinsPlay (pairPlay receiver sender env) := by
    rw [pairPlay,treeOfPair_ofTree (senderOblivious_narrowedInducedTree guard _)]
    exact (guard.lift_winningTree_iff tree).mp (narrowedInducedTree_winningTree_of_allThreadsWin guard winning) env
  have subset := ((phaseOfferMonitor_wins_iff _ _ _ _ _ _ _).mp guarded).2 node.length
  have initial : state.2.2 = decide (List.length (boundaryPhaseWord d h a) = 0) := by
    rw [flag]
    simp only [node,leftHandoverNode,List.length_map]
  have member : certificateHandover (numberedLeaderSlot objective header ∘ Subtype.val) (fun q => q.2 ()) move ∈
      numberedLeftCollect M objective rank header state (pairPlay receiver sender env node.length) := by
    change _ ∈ graphClosingOffers M state.1.1 state.1.2.1 nowShape state.2.2
      (leaderAnnotationStep M objective rank) state.1.2.2 (closingPolicyOfBank bank) _ _
    rw [initial]
    exact offered
  exact ⟨n,root,move,age,actual,realizes,subset member⟩

end
end Characterisation
