/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.LiveScheduledCoverage
import DistributedSynthesis.Library.Distributed.LeaderPhases.ClosingGraphExistence

/-! Populate the scheduled private-input closing checker using computed
flags from the checked per-root graph scan. Boundary truth on forbidden
histories and a separate target-coverage premise are unnecessary. -/
namespace Characterisation
open DistributedSynthesis

/-- The graph bank and live activity invariant supply the earlier checker
with complete scheduled transitions. Allowed targets remain unrestricted;
global winning successor compatibility is a separate obligation. -/
theorem graph_coupled_scheduled_bundle_exists {I₁ I₂ O₁ O₂ Q GQ : Type} {B K : Nat}
    [Fintype GQ] [DecidableEq GQ]
    [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
    [DecidableEq O₁] [DecidableEq O₂] [DecidableEq Q] [Nonempty O₁] [Nonempty O₂]
    (M : Recognizer Graph GQ) [DecidablePred (· ∈ M.accept)]
    (P : List Graph → Prop) (closed : PrefixClosed P)
    (recognizes : ∀ g, P g ↔ M.eval g ∈ M.accept) (d : Nat)
    (recent : ∀ g, P g → ∃ p, RecentOther P d g p)
    (u word : EnvHistory I₁ I₂) (liveU : P (History.graphSequence u))
    (startU : leaderBoundary P d u = true)
    [Fintype (InputHistoryComponent P u)] [DecidableEq (InputHistoryComponent P u)]
    (shape : InputShape (InputHistoryComponent P u))
    (rep : RepresentsInputShape (carriedBoundarySources P u word) shape)
    (active : InputHistoryComponent P u → Bool)
    (exactActivity : SourceActivityOnLive P d (List.length u) (List.length u + List.length word)
      (carriedBoundarySources P u word) active)
    (graphSource : InputHistoryComponent P u → GraphRootState GQ d K)
    (sourceExact : ∀ h, GraphRootRep P M (History.graphSequence (carriedBoundarySources P u word h)) (graphSource h))
    (table : ClosingGraphTable (InputHistoryComponent P u) I₁ I₂ GQ d K (d+1))
    (graphChecked : checkClosingGraphTable M graphSource table = true)
    (small : ∀ h : EnvHistory I₁ I₂, P (History.graphSequence h) → leaderBoundary P d h = true →
      Nat.card (InputHistoryComponent P h) ≤ B)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (initial : InputHistoryComponent P u → Q)
    (out : ClosingPolicy (InputHistoryComponent P u) I₁ I₂ O₁ O₂ (d+1))
    (coherent : ClosingPolicyCoherent shape out) :
    ∃ bundle : FirstExitBundle (ActiveClosingRoots active) I₁ I₂ O₁ O₂ Q B (d+1),
      bundle.1 = restrictClosingPolicy Subtype.val out ∧
      checkScheduledExitBundle (restrictInputShape shape Subtype.val) (decide (List.length word = 0))
        (restrictClosingFlags Subtype.val (closingGraphBoundaryTable M table)) (restrictClosingFlags Subtype.val (closingGraphLiveTable table))
        step (initial ∘ Subtype.val) (fun _ => True) (restrictClosingPolicy Subtype.val out) bundle = true := by
  let f : ActiveClosingRoots active → InputHistoryComponent P u := Subtype.val
  let past := carriedBoundarySources P u word
  let boundary := closingGraphBoundaryTable M table
  let live := closingGraphLiveTable table
  have liveExact := closingGraphLiveTable_exact M P closed recognizes past graphSource sourceExact table graphChecked
  have flags := closingGraphFlags_exact_on_live M P closed recognizes past graphSource sourceExact table graphChecked
  have restrictedLive : ∀ m s, restrictClosingFlags f live m s = true ↔
      P (History.graphSequence (closingLayerHistory (past ∘ f) m.val s)) := by
    intro m s
    simpa only [restrictClosingFlags,closingLayerHistory_map] using liveExact m (mapClosingLayer f m.val s)
  apply scheduled_first_exit_bundle_exists P (past ∘ f)
    ((carriedBoundarySources_injective P u word).comp Subtype.val_injective)
    (restrictInputShape shape f) (restrictInputShape_exact past shape rep f)
    (List.length u + List.length word) (fun h => carriedBoundarySources_depth P u word (f h))
    (decide (List.length word = 0)) (restrictClosingFlags f boundary) (restrictClosingFlags f live)
    restrictedLive step (initial ∘ f) (restrictClosingPolicy f out)
    (restrictClosingPolicy_coherent past shape rep _ (carriedBoundarySources_depth P u word) f out coherent)
  · intro n root scheduled alive exit
    have liveRoot := (closingLiveTable_exact P (past ∘ f) (restrictClosingFlags f live) restrictedLive
      (n.val+1) (by omega) root).mp alive
    have flagEq : closingFlagAt (restrictClosingFlags f boundary) =
        fun m s => closingFlagAt boundary m (mapClosingLayer f m s) := by
      funext m s
      exact closingFlagAt_restrict f boundary m s
    rw [flagEq] at exit
    exact scheduled_active_coverage_on_live P closed d recent u word liveU startU active exactActivity
      (closingFlagAt boundary) flags n scheduled root liveRoot exit
  · intro n root _ alive exit
    have liveRoot := (closingLiveTable_exact P (past ∘ f) (restrictClosingFlags f live) restrictedLive
      (n.val+1) (by omega) root).mp alive
    apply small _ liveRoot
    have oldExit : closingFirstExit (closingFlagAt boundary) (n.val+1) (mapClosingLayer f (n.val+1) root) = true := by
      simpa only [closingFirstExit_restrict] using exit
    have oldLive : P (History.graphSequence (closingLayerHistory past (n.val+1) (mapClosingLayer f (n.val+1) root))) := by
      simpa only [closingLayerHistory_map] using liveRoot
    have phase := live_carried_first_exit_phase P closed d recent u word liveU startU active exactActivity
      (closingFlagAt boundary) flags n _ oldLive (activeClosingLayer_root_alive active (n.val+1) root) oldExit
    simpa only [closingLayerHistory_map] using phase.end_boundary

/-- Both the checked graph scan and the accepted scheduled successor bundle
exist from the source invariants and uniform graph/input boundary bounds. -/
theorem exists_graph_coupled_closing {I₁ I₂ O₁ O₂ Q GQ : Type} {B K : Nat}
    [Fintype GQ] [DecidableEq GQ]
    [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
    [DecidableEq O₁] [DecidableEq O₂] [DecidableEq Q] [Nonempty O₁] [Nonempty O₂]
    (M : Recognizer Graph GQ) [DecidablePred (· ∈ M.accept)]
    (P : List Graph → Prop) (closed : PrefixClosed P)
    (recognizes : ∀ g, P g ↔ M.eval g ∈ M.accept) (d : Nat)
    (recent : ∀ g, P g → ∃ p, RecentOther P d g p)
    (u word : EnvHistory I₁ I₂) (liveU : P (History.graphSequence u))
    (startU : leaderBoundary P d u = true)
    [Fintype (InputHistoryComponent P u)] [DecidableEq (InputHistoryComponent P u)]
    (shape : InputShape (InputHistoryComponent P u))
    (rep : RepresentsInputShape (carriedBoundarySources P u word) shape)
    (active : InputHistoryComponent P u → Bool)
    (exactActivity : SourceActivityOnLive P d (List.length u) (List.length u + List.length word)
      (carriedBoundarySources P u word) active)
    (graphSource : InputHistoryComponent P u → GraphRootState GQ d K)
    (sourceExact : ∀ h, GraphRootRep P M (History.graphSequence (carriedBoundarySources P u word h)) (graphSource h))
    (graphBounded : ∀ g, P g → Finite (HistoryComponent P g) ∧ Nat.card (HistoryComponent P g) ≤ K)
    (small : ∀ h : EnvHistory I₁ I₂, P (History.graphSequence h) → leaderBoundary P d h = true →
      Nat.card (InputHistoryComponent P h) ≤ B)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (initial : InputHistoryComponent P u → Q)
    (out : ClosingPolicy (InputHistoryComponent P u) I₁ I₂ O₁ O₂ (d+1))
    (coherent : ClosingPolicyCoherent shape out) :
    ∃ table : ClosingGraphTable (InputHistoryComponent P u) I₁ I₂ GQ d K (d+1),
      checkClosingGraphTable M graphSource table = true ∧
    ∃ bundle : FirstExitBundle (ActiveClosingRoots active) I₁ I₂ O₁ O₂ Q B (d+1),
      bundle.1 = restrictClosingPolicy Subtype.val out ∧
      checkScheduledExitBundle (restrictInputShape shape Subtype.val) (decide (List.length word = 0))
        (restrictClosingFlags Subtype.val (closingGraphBoundaryTable M table)) (restrictClosingFlags Subtype.val (closingGraphLiveTable table))
        step (initial ∘ Subtype.val) (fun _ => True) (restrictClosingPolicy Subtype.val out) bundle = true := by
  obtain ⟨table,checked⟩ := exists_checked_closing_graph_table M P closed recognizes graphBounded
    (carriedBoundarySources P u word) graphSource sourceExact (d+1)
  refine ⟨table,checked,?_⟩
  exact graph_coupled_scheduled_bundle_exists M P closed recognizes d recent u word liveU startU
    shape rep active exactActivity graphSource sourceExact table checked small step initial out coherent

end Characterisation
