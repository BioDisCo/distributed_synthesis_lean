/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.NumberedLeaderExtraction

/-! Concrete successor components of the numbered phase collector. The
source histories occur only in the interpretation proof; the running table,
graph bank, and advertised outcomes use the fixed numbered alphabet. -/
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
variable (P : List Graph → Prop) (closed : PrefixClosed P)
variable (recognizes : ∀ g, P g ↔ M.eval g ∈ M.accept)
variable (recent : ∀ g, P g → ∃ p, RecentOther P d g p)
variable (bounded : ∀ g, P g → Finite (HistoryComponent P g) ∧ Nat.card (HistoryComponent P g) ≤ K)
variable (u : EnvHistory I₁ I₂) (e : Fin header.1.val ≃ InputHistoryComponent P u)
variable (liveU : P (History.graphSequence u)) (startU : leaderBoundary P d u = true)
variable (shape : RepresentsInputShape (fun h => (e h).val) header.2.1)
variable (graphs : ∀ h, GraphRootRep P M (History.graphSequence (e h).val) (header.2.2 h).1.1)

def NumberedPhaseSuccessor
    (bank : ClosingPlanBank (Fin header.1.val) I₁ I₂ O₁ O₂ d)
    (receiver : ReceiverBlockStrategy I₂ I₁ (RollingReceiverOutput (Fin header.1.val) I₁ I₂ O₁ O₂ d))
    (leader : SenderBlockStrategy I₁ (ShapeLeaderGroup header.2.1 .one → O₁))
    (env : Nat → I₂ × I₁) (n : Nat)
    (outcome : NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective) : Prop :=
  let state := numberedPhaseRun M objective rank header bank receiver leader env n
  let past := rollingSourceHistory (fun h => (e h).val) (branchNode env n)
  ∃ (t : Fin (d+1)) (root : ClosingLayer (ActiveClosingRoots state.1.2.1) I₁ I₂ (t.val+1))
    (move : ClosingBoundaryCertificate (ActiveClosingRoots state.1.2.1) I₁ I₂ O₁ O₂
      (LeaderAnnotation (GQ:=GQ) (d:=d) (K:=K) (C:=C) objective) B (d+1) (t.val+1)),
    certificateHandover (numberedLeaderSlot objective header ∘ Subtype.val) (fun q => q.2 ()) move = outcome ∧
    ClosingOfferRealizes P (past ∘ Subtype.val) (leaderAnnotationStep M objective rank)
      (state.1.2.2 ∘ Subtype.val) (restrictClosingPolicy Subtype.val (closingPolicyOfBank state.2.1)) (by omega) root move ∧
    P (History.graphSequence (closingLayerHistory (past ∘ Subtype.val) (t.val+1) root)) ∧
    ∀ i, ConsecutiveLeaderBoundaries P d
      (closingLayerHistory (past ∘ Subtype.val) (t.val+1) (move.2.2.1 i)) (List.length u)

include closed recognizes recent bounded liveU startU shape graphs in
omit [Inhabited I₁] [Inhabited I₂] in
/-- Every numbered offer is a complete actual successor of this boundary
family. Coverage follows from the existing canonical schedule after reindexing;
neither coverage nor a separate realization per target slot is assumed. -/
theorem numberedPhaseRun_offer_realizes
    (bank : ClosingPlanBank (Fin header.1.val) I₁ I₂ O₁ O₂ d)
    (receiver : ReceiverBlockStrategy I₂ I₁ (RollingReceiverOutput (Fin header.1.val) I₁ I₂ O₁ O₂ d))
    (leader : SenderBlockStrategy I₁ (ShapeLeaderGroup header.2.1 .one → O₁))
    (env : Nat → I₂ × I₁) (n : Nat)
    (outcome : NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)
    (offered : outcome ∈ jointGraphLeaderCollect M (leaderAnnotationStep M objective rank)
      header.2.1 (numberedLeaderSlot objective header) (fun q => q.2 ())
      (numberedPhaseRun M objective rank header bank receiver leader env n) (pairPlay receiver leader env n)) :
    NumberedPhaseSuccessor M objective rank header P u e bank receiver leader env n outcome := by
  let past := fun h => (e h).val
  let node := branchNode env n
  let word := rightInputHistory node
  let state := numberedPhaseRun M objective rank header bank receiver leader env n
  have depth : ∀ h, List.length (past h) = List.length u :=
    fun h => (inputConnected_length P (e h).property).symm
  have nodeLength : node.length = n := TreeNonemptiness.branch_length env n
  have wordLength : List.length word = n := by
    simpa only [word,rightInputHistory,List.length_map] using nodeLength
  have nodeEmpty : (node = []) ↔ n = 0 := by rw [← List.length_eq_zero_iff,nodeLength]
  have current := jointGraphLeaderMemory_rolling_sources M P closed recognizes bounded
    past (List.length u) depth (fun i => (header.2.2 i).1.1) graphs
    (leaderAnnotationStep M objective rank) (fun i => resetLeaderMinimum objective (header.2.2 i))
    (shapeLeaderGroup header.2.1 .one) bank receiver leader env n
  have currentShape : RepresentsInputShape (carriedBoundarySources P u word ∘ e)
      (jointLeaderShape header.2.1 (decide (n = 0))) := by
    simpa only [nodeEmpty] using jointLeaderShape_exact past header.2.1 shape node
  have flag : state.2.2 = decide (List.length word = 0) := by
    rw [wordLength]
    exact current.2.2.2
  change outcome ∈ graphClosingOffers M state.1.1 state.1.2.1
    (jointLeaderShape header.2.1 state.2.2) state.2.2 (leaderAnnotationStep M objective rank) state.1.2.2
    (closingPolicyOfBank state.2.1) (numberedLeaderSlot objective header) (fun q => q.2 ()) at offered
  rw [flag,wordLength] at offered
  have activity : SourceActivityOnLive P d (List.length u) (List.length u + List.length word)
      (carriedBoundarySources P u word ∘ e) state.1.2.1 := by
    rw [wordLength]
    exact current.2.1
  have offered' : outcome ∈ graphClosingOffers M state.1.1 state.1.2.1
      (jointLeaderShape header.2.1 (decide (n = 0))) (decide (List.length word = 0))
      (leaderAnnotationStep M objective rank) state.1.2.2 (closingPolicyOfBank state.2.1)
      (numberedLeaderSlot objective header) (fun q => q.2 ()) := by
    simpa only [wordLength] using offered
  exact numbered_graphClosingOffers_live_realizes M P closed recognizes d recent u word e liveU startU
    _ currentShape state.1.2.1 activity state.1.1 current.1 (leaderAnnotationStep M objective rank)
    state.1.2.2 (closingPolicyOfBank state.2.1) (numberedLeaderSlot objective header) (fun q => q.2 ())
    outcome offered'

include closed recognizes recent bounded liveU startU shape graphs in
/-- The original winning continuation supplies a legal move in one fixed
finite numbered game alphabet. Every advertised outcome has a complete
successor under that same original strategy and common input branch. -/
theorem numbered_right_with_complete_successors
    (σ : StrategyPair I₁ I₂ O₁ O₂)
    (winning : ContinuationWins objective.AcceptsFrom (fun i => (header.2.2 i).1.2)
      (strategyContinuationPolicy σ (fun h => (e h).val))) :
    ∃ base : ShapeLeaderGroup header.2.1 .one → View I₁ I₂ .one,
      Function.Injective base ∧
      (∀ h, currentView .one (e h).val = base (shapeLeaderGroup header.2.1 .one h)) ∧
      ∃ permitted : Finset (NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective),
        numberedRightLegal M objective rank header permitted = true ∧
        ∀ outcome, outcome ∈ permitted → ∃ env n,
          NumberedPhaseSuccessor M objective rank header P u e
            (rollingOriginalBank σ (fun h => (e h).val) d [])
            (rollingOriginalReceiver σ (fun h => (e h).val) d)
            (jointOriginalLeader σ base) env n outcome := by
  obtain ⟨base,distinct,same,permitted,legal,witnesses⟩ :=
    numbered_right_of_strategy M objective rank header (fun h => (e h).val) shape
      (List.length u) (fun h => (inputConnected_length P (e h).property).symm) σ winning
  refine ⟨base,distinct,same,permitted,legal,?_⟩
  intro outcome member
  obtain ⟨env,n,offered⟩ := witnesses outcome member
  exact ⟨env,n,numberedPhaseRun_offer_realizes M objective rank header P closed recognizes recent bounded
    u e liveU startU shape graphs (rollingOriginalBank σ (fun h => (e h).val) d [])
    (rollingOriginalReceiver σ (fun h => (e h).val) d) (jointOriginalLeader σ base) env n outcome offered⟩

end
end Characterisation
