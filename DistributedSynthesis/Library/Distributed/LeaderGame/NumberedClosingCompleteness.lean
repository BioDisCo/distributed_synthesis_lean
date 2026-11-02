/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.NumberedBoundaryCoverage
import DistributedSynthesis.Library.Distributed.LeaderPhases.GraphClosingOfferCompleteness

/-! Completeness of the numbered collector. The proof constructs a graph
scan and a complete certificate for the actual exit. A numbering of the
source component adds no target-coverage or certificate-existence premise. -/
namespace Characterisation
open DistributedSynthesis

section
variable {H I₁ I₂ O₁ O₂ Q GQ : Type} {B C K : Nat}
variable [Fintype H] [DecidableEq H] [Fintype GQ] [DecidableEq GQ] [Fintype Q] [DecidableEq Q]
variable [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
variable [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂]
variable [Nonempty O₁] [Nonempty O₂]
variable (M : Recognizer Graph GQ) [DecidablePred (· ∈ M.accept)]
variable (P : List Graph → Prop) (closed : PrefixClosed P)
variable (recognizes : ∀ g, P g ↔ M.eval g ∈ M.accept) (d : Nat)
variable (recent : ∀ g, P g → ∃ p, RecentOther P d g p)
variable (u word : EnvHistory I₁ I₂) (e : H ≃ InputHistoryComponent P u)
variable (liveU : P (History.graphSequence u)) (startU : leaderBoundary P d u = true)
variable (shape : InputShape H)
variable (rep : RepresentsInputShape (carriedBoundarySources P u word ∘ e) shape)
variable (active : H → Bool)
variable (activity : SourceActivityOnLive P d (List.length u) (List.length u + List.length word)
  (carriedBoundarySources P u word ∘ e) active)
variable (source : H → GraphRootState GQ d K)
variable (sourceExact : ∀ h, GraphRootRep P M
  (History.graphSequence ((carriedBoundarySources P u word ∘ e) h)) (source h))
variable (graphBounded : ∀ g, P g → Finite (HistoryComponent P g) ∧ Nat.card (HistoryComponent P g) ≤ K)
variable (small : ∀ h : EnvHistory I₁ I₂, P (History.graphSequence h) → leaderBoundary P d h = true →
  Nat.card (InputHistoryComponent P h) ≤ B)
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (initial : H → Q)
variable (expected : ClosingPolicy H I₁ I₂ O₁ O₂ (d+1))
variable (coherent : ClosingPolicyCoherent shape expected)
variable (slot : H → Fin (B+1)) (minimum : Q → Fin (C+1))

include closed recognizes recent liveU startU rep activity sourceExact graphBounded small coherent in
theorem numbered_graphClosingOffers_complete
    (n : Fin (d+1)) (root : ClosingLayer (ActiveClosingRoots active) I₁ I₂ (n.val+1))
    (scheduled : closingWindowScheduled (decide (List.length word = 0)) (d+1) (n.val+1) = true)
    (liveRoot : P (History.graphSequence
      (closingLayerHistory ((carriedBoundarySources P u word ∘ e) ∘ Subtype.val) (n.val+1) root)))
    (phase : ConsecutiveLeaderBoundaries P d
      (closingLayerHistory ((carriedBoundarySources P u word ∘ e) ∘ Subtype.val) (n.val+1) root)
      (List.length u)) :
    ∃ move : ClosingBoundaryCertificate (ActiveClosingRoots active) I₁ I₂ O₁ O₂ Q B (d+1) (n.val+1),
      move.2.1 = restrictClosingPolicy Subtype.val expected ∧
      ClosingOfferRealizes P ((carriedBoundarySources P u word ∘ e) ∘ Subtype.val)
        step (initial ∘ Subtype.val) (restrictClosingPolicy Subtype.val expected) (by omega) root move ∧
      certificateHandover (slot ∘ Subtype.val) minimum move ∈
        graphClosingOffers M source active shape (decide (List.length word = 0)) step initial expected slot minimum := by
  let past := carriedBoundarySources P u word ∘ e
  let f : ActiveClosingRoots active → H := Subtype.val
  let L := List.length u + List.length word
  have depth : ∀ h, List.length (past h) = L := fun h => carriedBoundarySources_depth P u word (e h)
  obtain ⟨table,graphChecked⟩ := exists_checked_closing_graph_table M P closed recognizes graphBounded
    past source sourceExact (d+1)
  let boundary := closingGraphBoundaryTable M table
  let live := closingGraphLiveTable table
  have liveExact := closingGraphLiveTable_exact M P closed recognizes past source sourceExact table graphChecked
  have flags := closingGraphFlags_exact_on_live M P closed recognizes past source sourceExact table graphChecked
  have restrictedLive : ∀ m s, restrictClosingFlags f live m s = true ↔
      P (History.graphSequence (closingLayerHistory (past ∘ f) m.val s)) := by
    intro m s
    simpa only [restrictClosingFlags,closingLayerHistory_map] using liveExact m (mapClosingLayer f m.val s)
  have exactLive := closingLiveTable_exact P (past ∘ f) (restrictClosingFlags f live)
    restrictedLive (n.val+1) (by omega)
  have alive := (exactLive root).mpr liveRoot
  have oldLive : P (History.graphSequence (closingLayerHistory past (n.val+1) (mapClosingLayer f (n.val+1) root))) := by
    simpa only [past,f,closingLayerHistory_map] using liveRoot
  have oldExit : closingFirstExit (closingFlagAt boundary) (n.val+1) (mapClosingLayer f (n.val+1) root) = true := by
    apply (closingFirstExit_exact_on_live P closed d past L depth (closingFlagAt boundary) (d+1)
      flags n.val (by omega) _ oldLive).mpr
    constructor
    · intro m lo hi
      rw [← closingLayerHistory_map]
      apply phase.no_boundary m (by dsimp [L] at lo; omega)
      rw [closingLayerHistory_length (past ∘ f) L (fun h => depth (f h))]
      exact hi
    · simpa only [past,f,closingLayerHistory_map] using phase.end_boundary
  have exit : closingFirstExit (closingFlagAt (restrictClosingFlags f boundary)) (n.val+1) root = true := by
    simpa only [closingFirstExit_restrict] using oldExit
  have exit' : closingFirstExit (fun m s => closingFlagAt boundary m (mapClosingLayer f m s)) (n.val+1) root = true := by
    simpa only [closingFirstExit_map] using oldExit
  have covers := numbered_scheduled_active_coverage P closed d recent u word e liveU startU active activity
    (closingFlagAt boundary) flags n scheduled root liveRoot exit'
  have unique : Function.Injective (past ∘ f) :=
    ((carriedBoundarySources_injective P u word).comp e.injective).comp Subtype.val_injective
  have shapeExact := restrictInputShape_exact past shape rep f
  obtain ⟨move,policy,checked⟩ := exists_checked_closing_boundary_of_target_coverage P (past ∘ f) unique
    (restrictInputShape shape f) shapeExact L (fun h => depth (f h)) step (initial ∘ f)
    (restrictClosingPolicy f expected)
    (restrictClosingPolicy_coherent past shape rep L depth f expected coherent) (show n.val+1 ≤ d+1 by omega)
    (closingFlagAt (restrictClosingFlags f live) (n.val+1)) exactLive root liveRoot covers
    (small _ liveRoot phase.end_boundary)
  have member := (mem_scheduledClosingCertificates_iff _ _ _ _ _ _ _ n root move).mpr
    ⟨⟨scheduled,alive,exit,policy⟩,checked⟩
  refine ⟨move,policy,?_,?_⟩
  · exact scheduledClosingCertificate_realizes P (past ∘ f) unique (restrictInputShape shape f)
      shapeExact L (fun h => depth (f h)) (decide (List.length word = 0))
      (restrictClosingFlags f boundary) (restrictClosingFlags f live) restrictedLive
      step (initial ∘ f) (restrictClosingPolicy f expected) n root move member covers
  · apply (mem_graphClosingOffers_iff M source active shape _ step initial expected slot minimum _).mpr
    refine ⟨table,graphChecked,?_⟩
    exact (mem_scheduledClosingOffers_iff _ _ _ _ _ _ _ _ _ _).mpr ⟨n,root,move,member,rfl⟩

end
end Characterisation
