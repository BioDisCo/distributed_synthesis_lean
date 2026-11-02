/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.NumberedLeftSources

/-! Leftward advertised outcomes have complete successors under the same
original physical boundary rule as rightward outcomes. The existing generic
numbered closing-offer theorem supplies coverage and consecutive boundaries. -/
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

def NumberedLeftPhaseSuccessor
    (bank : ClosingPlanBank (Fin header.1.val) I₂ I₁ O₂ O₁ d)
    (receiver : ReceiverBlockStrategy I₁ I₂ (RollingReceiverOutput (Fin header.1.val) I₂ I₁ O₂ O₁ d))
    (leader : SenderBlockStrategy I₂ (ShapeLeaderGroup header.2.1 .two → O₂))
    (env : Nat → I₁ × I₂) (n : Nat)
    (outcome : NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective) : Prop :=
  let state := numberedLeftPhaseRun M objective rank header bank receiver leader env n
  let past := leftSourceHistory (fun h => (e h).val) (branchNode env n)
  ∃ (t : Fin (d+1)) (root : ClosingLayer (ActiveClosingRoots state.1.2.1) I₁ I₂ (t.val+1))
    (move : ClosingBoundaryCertificate (ActiveClosingRoots state.1.2.1) I₁ I₂ O₁ O₂
      (LeaderAnnotation (GQ:=GQ) (d:=d) (K:=K) (C:=C) objective) B (d+1) (t.val+1)),
    certificateHandover (numberedLeaderSlot objective header ∘ Subtype.val) (fun q => q.2 ()) move = outcome ∧
    ClosingOfferRealizes P (past ∘ Subtype.val) (leaderAnnotationStep M objective rank)
      (state.1.2.2 ∘ Subtype.val)
      (restrictClosingPolicy Subtype.val (closingPolicyOfBank (fun h => exchangePlan (state.2.1 h))))
      (by omega) root move ∧
    P (History.graphSequence (closingLayerHistory (past ∘ Subtype.val) (t.val+1) root)) ∧
    ∀ i, ConsecutiveLeaderBoundaries P d
      (closingLayerHistory (past ∘ Subtype.val) (t.val+1) (move.2.2.1 i)) (List.length u)

include closed recognizes recent bounded liveU startU shape graphs in
omit [Inhabited I₁] [Inhabited I₂] in
theorem numberedLeftPhaseRun_offer_realizes
    (bank : ClosingPlanBank (Fin header.1.val) I₂ I₁ O₂ O₁ d)
    (receiver : ReceiverBlockStrategy I₁ I₂ (RollingReceiverOutput (Fin header.1.val) I₂ I₁ O₂ O₁ d))
    (leader : SenderBlockStrategy I₂ (ShapeLeaderGroup header.2.1 .two → O₂))
    (env : Nat → I₁ × I₂) (n : Nat)
    (outcome : NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)
    (offered : outcome ∈ numberedLeftCollect M objective rank header
      (numberedLeftPhaseRun M objective rank header bank receiver leader env n) (pairPlay receiver leader env n)) :
    NumberedLeftPhaseSuccessor M objective rank header P u e bank receiver leader env n outcome := by
  let past := fun h => (e h).val
  let node := branchNode env n
  let word := leftInputHistory node
  let state := numberedLeftPhaseRun M objective rank header bank receiver leader env n
  have depth : ∀ h, List.length (past h) = List.length u :=
    fun h => (inputConnected_length P (e h).property).symm
  have nodeLength : node.length = n := TreeNonemptiness.branch_length env n
  have wordLength : List.length word = n := by
    simpa only [word,leftInputHistory,List.length_map] using nodeLength
  have nodeEmpty : (node = []) ↔ n = 0 := by rw [← List.length_eq_zero_iff,nodeLength]
  have current := numberedLeftPhaseRun_sources M objective rank header bank receiver leader env
    P closed recognizes bounded past (List.length u) depth graphs n
  have currentShape : RepresentsInputShape (carriedBoundarySources P u word ∘ e)
      (exchangeShape (jointLeaderShape (exchangeShape header.2.1) (decide (n = 0)))) := by
    simpa only [nodeEmpty] using leftLeaderShape_exact past header.2.1 shape node
  have flag : state.2.2 = decide (List.length word = 0) := by
    rw [wordLength]
    exact current.2.2.2
  change outcome ∈ graphClosingOffers M state.1.1 state.1.2.1
    (exchangeShape (jointLeaderShape (exchangeShape header.2.1) state.2.2)) state.2.2
    (leaderAnnotationStep M objective rank) state.1.2.2
    (closingPolicyOfBank (fun h => exchangePlan (state.2.1 h)))
    (numberedLeaderSlot objective header) (fun q => q.2 ()) at offered
  rw [flag,wordLength] at offered
  have activity : SourceActivityOnLive P d (List.length u) (List.length u + List.length word)
      (carriedBoundarySources P u word ∘ e) state.1.2.1 := by
    rw [wordLength]
    exact current.2.1
  have offered' : outcome ∈ graphClosingOffers M state.1.1 state.1.2.1
      (exchangeShape (jointLeaderShape (exchangeShape header.2.1) (decide (n = 0))))
      (decide (List.length word = 0)) (leaderAnnotationStep M objective rank) state.1.2.2
      (closingPolicyOfBank (fun h => exchangePlan (state.2.1 h)))
      (numberedLeaderSlot objective header) (fun q => q.2 ()) := by
    simpa only [wordLength] using offered
  exact numbered_graphClosingOffers_live_realizes M P closed recognizes d recent u word e liveU startU
    _ currentShape state.1.2.1 activity state.1.1 current.1 (leaderAnnotationStep M objective rank)
    state.1.2.2 (closingPolicyOfBank (fun h => exchangePlan (state.2.1 h)))
    (numberedLeaderSlot objective header) (fun q => q.2 ()) outcome offered'

include closed recognizes recent bounded liveU startU shape graphs in
/-- The leftward analogue of numbered_right_with_complete_successors uses
exactly the same original P and leaderBoundary P d in its conclusion. -/
theorem numbered_left_with_complete_successors
    (σ : StrategyPair I₁ I₂ O₁ O₂)
    (winning : ContinuationWins objective.AcceptsFrom (fun i => (header.2.2 i).1.2)
      (strategyContinuationPolicy σ (fun h => (e h).val))) :
    ∃ base : ShapeLeaderGroup header.2.1 .two → View I₂ I₁ .one,
      Function.Injective base ∧
      (∀ h, currentView .one (exchangeHistory (e h).val) = base (shapeLeaderGroup header.2.1 .two h)) ∧
      ∃ permitted : Finset (NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective),
        numberedLeftLegal M objective rank header permitted = true ∧
        ∀ outcome, outcome ∈ permitted → ∃ env n,
          NumberedLeftPhaseSuccessor M objective rank header P u e
            (rollingOriginalBank (exchangeStrategy σ) (exchangeHistory ∘ fun h => (e h).val) d [])
            (rollingOriginalReceiver (exchangeStrategy σ) (exchangeHistory ∘ fun h => (e h).val) d)
            (jointOriginalLeader (exchangeStrategy σ) base) env n outcome := by
  obtain ⟨base,distinct,same,permitted,legal,witnesses⟩ :=
    numbered_left_of_strategy M objective rank header (fun h => (e h).val) shape
      (List.length u) (fun h => (inputConnected_length P (e h).property).symm) σ winning
  refine ⟨base,distinct,same,permitted,legal,?_⟩
  intro outcome member
  obtain ⟨env,n,offered⟩ := witnesses outcome member
  exact ⟨env,n,numberedLeftPhaseRun_offer_realizes M objective rank header P closed recognizes recent bounded
    u e liveU startU shape graphs
    (rollingOriginalBank (exchangeStrategy σ) (exchangeHistory ∘ fun h => (e h).val) d [])
    (rollingOriginalReceiver (exchangeStrategy σ) (exchangeHistory ∘ fun h => (e h).val) d)
    (jointOriginalLeader (exchangeStrategy σ) base) env n outcome offered⟩

end
end Characterisation
