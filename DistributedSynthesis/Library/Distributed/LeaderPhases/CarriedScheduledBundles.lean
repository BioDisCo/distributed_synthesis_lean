/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.ScheduledExitBundles

/-! The canonical checker can be populated from each carried boundary
family without assuming coverage separately for its demanded exits. -/
namespace Characterisation
open DistributedSynthesis

/-- Exact carried data and the uniform size bound at agreed boundaries
suffice. Complete coverage is derived from the schedule and activity invariant.
The target predicate is unrestricted; global winning closure is not asserted. -/
theorem carried_scheduled_bundle_exists {I₁ I₂ O₁ O₂ Q : Type} {B : Nat}
    [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
    [DecidableEq O₁] [DecidableEq O₂] [DecidableEq Q] [Nonempty O₁] [Nonempty O₂]
    (P : List Graph → Prop) (closed : PrefixClosed P) (d : Nat)
    (recent : ∀ g, P g → ∃ p, RecentOther P d g p)
    (u word : EnvHistory I₁ I₂) (liveU : P (History.graphSequence u))
    (startU : leaderBoundary P d u = true)
    [Fintype (InputHistoryComponent P u)] [DecidableEq (InputHistoryComponent P u)]
    (shape : InputShape (InputHistoryComponent P u))
    (rep : RepresentsInputShape (carriedBoundarySources P u word) shape)
    (active : InputHistoryComponent P u → Bool)
    (exactActivity : SourceActivityExact P d (List.length u) (List.length u + List.length word)
      (carriedBoundarySources P u word) active)
    (boundary live : ClosingFlagTable (InputHistoryComponent P u) I₁ I₂ (d+1))
    (exactFlags : ∀ m s, boundary m s =
      leaderBoundary P d (closingLayerHistory (carriedBoundarySources P u word) m.val s))
    (liveExact : ∀ m s, live m s = true ↔
      P (History.graphSequence (closingLayerHistory (carriedBoundarySources P u word) m.val s)))
    (small : ∀ h : EnvHistory I₁ I₂, P (History.graphSequence h) → leaderBoundary P d h = true →
      Nat.card (InputHistoryComponent P h) ≤ B)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (initial : InputHistoryComponent P u → Q)
    (out : ClosingPolicy (InputHistoryComponent P u) I₁ I₂ O₁ O₂ (d+1))
    (coherent : ClosingPolicyCoherent shape out) :
    ∃ bundle : FirstExitBundle (ActiveClosingRoots active) I₁ I₂ O₁ O₂ Q B (d+1),
      bundle.1 = restrictClosingPolicy Subtype.val out ∧
      checkScheduledExitBundle (restrictInputShape shape Subtype.val) (decide (List.length word = 0))
        (restrictClosingFlags Subtype.val boundary) (restrictClosingFlags Subtype.val live)
        step (initial ∘ Subtype.val) (fun _ => True) (restrictClosingPolicy Subtype.val out) bundle = true := by
  let f : ActiveClosingRoots active → InputHistoryComponent P u := Subtype.val
  let past := carriedBoundarySources P u word
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
    exact scheduled_active_root_coverage P closed d recent u word liveU startU active exactActivity
      boundary exactFlags n scheduled root liveRoot exit
  · intro n root _ alive exit
    have liveRoot := (closingLiveTable_exact P (past ∘ f) (restrictClosingFlags f live) restrictedLive
      (n.val+1) (by omega) root).mp alive
    apply small _ liveRoot
    have oldExit : closingFirstExit (closingFlagAt boundary) (n.val+1) (mapClosingLayer f (n.val+1) root) = true := by
      simpa only [closingFirstExit_restrict] using exit
    have phase := carried_active_first_exit_phase P closed d recent u word liveU startU active exactActivity
      boundary exactFlags n _ (activeClosingLayer_root_alive active (n.val+1) root) oldExit
    simpa only [closingLayerHistory_map] using phase.end_boundary

end Characterisation
