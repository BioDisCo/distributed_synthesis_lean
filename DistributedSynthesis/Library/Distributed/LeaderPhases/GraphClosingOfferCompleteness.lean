/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.GraphClosingOfferSoundness

/-! Every actual scheduled live exit produces a collected certificate.
Graph scans and target certificates are supplied by the existing existence
proofs, rather than by additional hypotheses on the local strategy. -/
namespace Characterisation
open DistributedSynthesis

section
variable {I₁ I₂ O₁ O₂ Q GQ : Type} {B C K : Nat}
variable [Fintype GQ] [DecidableEq GQ] [Fintype Q] [DecidableEq Q]
variable [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
variable [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂]
variable [Nonempty O₁] [Nonempty O₂]
variable (M : Recognizer Graph GQ) [DecidablePred (· ∈ M.accept)]
variable (P : List Graph → Prop) (closed : PrefixClosed P)
variable (recognizes : ∀ g, P g ↔ M.eval g ∈ M.accept) (d : Nat)
variable (recent : ∀ g, P g → ∃ p, RecentOther P d g p)
variable (u word : EnvHistory I₁ I₂) (liveU : P (History.graphSequence u))
variable (startU : leaderBoundary P d u = true)
variable [Fintype (InputHistoryComponent P u)] [DecidableEq (InputHistoryComponent P u)]
variable (shape : InputShape (InputHistoryComponent P u))
variable (rep : RepresentsInputShape (carriedBoundarySources P u word) shape)
variable (active : InputHistoryComponent P u → Bool)
variable (activity : SourceActivityOnLive P d (List.length u) (List.length u + List.length word)
  (carriedBoundarySources P u word) active)
variable (source : InputHistoryComponent P u → GraphRootState GQ d K)
variable (sourceExact : ∀ h, GraphRootRep P M
  (History.graphSequence (carriedBoundarySources P u word h)) (source h))
variable (graphBounded : ∀ g, P g → Finite (HistoryComponent P g) ∧ Nat.card (HistoryComponent P g) ≤ K)
variable (small : ∀ h : EnvHistory I₁ I₂, P (History.graphSequence h) → leaderBoundary P d h = true →
  Nat.card (InputHistoryComponent P h) ≤ B)
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
variable (initial : InputHistoryComponent P u → Q)
variable (expected : ClosingPolicy (InputHistoryComponent P u) I₁ I₂ O₁ O₂ (d+1))
variable (coherent : ClosingPolicyCoherent shape expected)
variable (slot : InputHistoryComponent P u → Fin (B+1)) (minimum : Q → Fin (C+1))

include closed recognizes recent liveU startU rep activity sourceExact graphBounded small coherent in
/-- No actual scheduled live exit is omitted. Its complete target family
is realized from the current sources under the same carried policy. -/
theorem graphClosingOffers_complete
    (n : Fin (d+1)) (root : ClosingLayer (ActiveClosingRoots active) I₁ I₂ (n.val+1))
    (scheduled : closingWindowScheduled (decide (List.length word = 0)) (d+1) (n.val+1) = true)
    (liveRoot : P (History.graphSequence
      (closingLayerHistory (carriedBoundarySources P u word ∘ Subtype.val) (n.val+1) root)))
    (phase : ConsecutiveLeaderBoundaries P d
      (closingLayerHistory (carriedBoundarySources P u word ∘ Subtype.val) (n.val+1) root) (List.length u)) :
    ∃ move : ClosingBoundaryCertificate (ActiveClosingRoots active) I₁ I₂ O₁ O₂ Q B (d+1) (n.val+1),
      move.2.1 = restrictClosingPolicy Subtype.val expected ∧
      ClosingOfferRealizes P (carriedBoundarySources P u word ∘ Subtype.val)
        step (initial ∘ Subtype.val) (restrictClosingPolicy Subtype.val expected) (by omega) root move ∧
      certificateHandover (slot ∘ Subtype.val) minimum move ∈
        graphClosingOffers M source active shape (decide (List.length word = 0)) step initial expected slot minimum := by
  obtain ⟨table,graphChecked,bundle,policy,bundleChecked⟩ := exists_graph_coupled_closing
    M P closed recognizes d recent u word liveU startU shape rep active activity source sourceExact
    graphBounded small step initial expected coherent
  let f : ActiveClosingRoots active → InputHistoryComponent P u := Subtype.val
  let past := carriedBoundarySources P u word
  let boundary := closingGraphBoundaryTable M table
  let live := closingGraphLiveTable table
  let L := List.length u + List.length word
  have depth := carriedBoundarySources_depth P u word
  have liveExact := closingGraphLiveTable_exact M P closed recognizes past source sourceExact table graphChecked
  have flags := closingGraphFlags_exact_on_live M P closed recognizes past source sourceExact table graphChecked
  have restrictedLive : ∀ m s, restrictClosingFlags f live m s = true ↔
      P (History.graphSequence (closingLayerHistory (past ∘ f) m.val s)) := by
    intro m s
    simpa only [restrictClosingFlags,closingLayerHistory_map] using liveExact m (mapClosingLayer f m.val s)
  have alive : closingFlagAt (restrictClosingFlags f live) (n.val+1) root = true :=
    (closingLiveTable_exact P (past ∘ f) (restrictClosingFlags f live) restrictedLive (n.val+1) (by omega) root).mpr liveRoot
  have oldLive : P (History.graphSequence (closingLayerHistory past (n.val+1) (mapClosingLayer f (n.val+1) root))) := by
    simpa only [closingLayerHistory_map] using liveRoot
  have oldExit : closingFirstExit (closingFlagAt boundary) (n.val+1) (mapClosingLayer f (n.val+1) root) = true := by
    apply (closingFirstExit_exact_on_live P closed d past L depth (closingFlagAt boundary) (d+1)
      flags n.val (by omega) _ oldLive).mpr
    constructor
    · intro m lo hi
      rw [← closingLayerHistory_map]
      apply phase.no_boundary m (by dsimp [L] at lo; omega)
      rw [closingLayerHistory_length (past ∘ f) L (fun h => depth (f h))]
      exact hi
    · simpa only [closingLayerHistory_map] using phase.end_boundary
  have exit : closingFirstExit (closingFlagAt (restrictClosingFlags f boundary)) (n.val+1) root = true := by
    simpa only [closingFirstExit_restrict] using oldExit
  have checked := (checkScheduledExitBundle_correct _ _ _ _ _ _ (fun _ => True) _ bundle).mp bundleChecked
  have each := checked.2.2 n root scheduled alive exit
  have member := (mem_scheduledClosingCertificates_iff _ _ _ _ _ _ _ n root (bundle.2 n root)).mpr
    ⟨⟨scheduled,alive,exit,each.1.trans policy⟩,each.2⟩
  have flagEq : closingFlagAt (restrictClosingFlags f boundary) =
      fun m s => closingFlagAt boundary m (mapClosingLayer f m s) := by
    funext m s
    exact closingFlagAt_restrict f boundary m s
  have exit' := exit
  rw [flagEq] at exit'
  have covers := scheduled_active_coverage_on_live P closed d recent u word liveU startU active activity
    (closingFlagAt boundary) flags n scheduled root liveRoot exit'
  have realization := scheduledClosingCertificate_realizes P (past ∘ f)
    ((carriedBoundarySources_injective P u word).comp Subtype.val_injective)
    (restrictInputShape shape f) (restrictInputShape_exact past shape rep f)
    L (fun h => depth (f h)) (decide (List.length word = 0)) (restrictClosingFlags f boundary)
    (restrictClosingFlags f live) restrictedLive step (initial ∘ f) (restrictClosingPolicy f expected)
    n root (bundle.2 n root) member covers
  refine ⟨bundle.2 n root,each.1.trans policy,realization,?_⟩
  exact graphClosingOffers_of_bundle M source active shape _ step initial expected slot minimum
    table graphChecked bundle bundleChecked n root scheduled alive exit

end
end Characterisation
