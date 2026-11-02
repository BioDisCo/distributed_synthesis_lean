/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.LiveClosingFlags

/-! The canonical coverage proof needs activity and boundary truth only on
live histories. This connects checked graph scans to the scheduled checker
without assigning semantic boundary flags to forbidden prefixes. -/
namespace Characterisation
open DistributedSynthesis

section Coverage
variable {I₁ I₂ : Type}
variable (P : List Graph → Prop) (closed : PrefixClosed P) (d : Nat)
variable (recent : ∀ g, P g → ∃ p, RecentOther P d g p)
variable (u word : EnvHistory I₁ I₂) (liveU : P (History.graphSequence u)) (startU : leaderBoundary P d u = true)
variable (active : InputHistoryComponent P u → Bool)
variable (activity : SourceActivityOnLive P d (List.length u) (List.length u + List.length word)
  (carriedBoundarySources P u word) active)
variable (boundary : (n : Nat) → ClosingLayer (InputHistoryComponent P u) I₁ I₂ n → Bool)
variable (flags : ∀ n, 0 < n → n ≤ d+1 → ∀ s,
  P (History.graphSequence (closingLayerHistory (carriedBoundarySources P u word) n s)) →
  boundary n s = leaderBoundary P d (closingLayerHistory (carriedBoundarySources P u word) n s))

include closed recent liveU startU activity flags in
theorem live_carried_first_exit_phase (n : Fin (d+1))
    (root : ClosingLayer (InputHistoryComponent P u) I₁ I₂ (n.val+1))
    (live : P (History.graphSequence (closingLayerHistory (carriedBoundarySources P u word) (n.val+1) root)))
    (alive : active (closingLayerRoot (n.val+1) root) = true)
    (exit : closingFirstExit boundary (n.val+1) root = true) :
    ConsecutiveLeaderBoundaries P d (closingLayerHistory (carriedBoundarySources P u word) (n.val+1) root) (List.length u) := by
  let past := carriedBoundarySources P u word
  let L := List.length u + List.length word
  have depth := carriedBoundarySources_depth P u word
  have later := (closingFirstExit_exact_on_live P closed d past L depth boundary (d+1) flags n.val (by omega) root live).mp exit
  have oldLive : P (History.graphSequence (past (closingLayerRoot (n.val+1) root))) := by
    rw [← closingLayerHistory_take_source past L depth (n.val+1) root]
    exact live_history_take P closed _ live L
  have before := (activity _ oldLive).mp alive
  refine ⟨by rw [closingLayerHistory_length past L depth]; dsimp [L]; omega,?_,later.2,?_⟩
  · rw [closingLayerHistory_take_before_source past L depth (n.val+1) root (List.length u) (by dsimp [L]; omega)]
    exact carriedBoundarySources_start P closed d recent u word liveU startU _
  · intro m lo hi
    by_cases early : m ≤ L
    · rw [closingLayerHistory_take_before_source past L depth (n.val+1) root m early]
      exact before m lo early
    · apply later.1 m (by omega)
      rwa [closingLayerHistory_length past L depth] at hi

include closed recent liveU startU activity flags in
/-- Complete target coverage remains valid for the computed activity bits
and computed live boundary flags, after restricting to active roots. -/
theorem scheduled_active_coverage_on_live (n : Fin (d+1))
    (scheduled : closingWindowScheduled (decide (List.length word = 0)) (d+1) (n.val+1) = true)
    (root : ClosingLayer (ActiveClosingRoots active) I₁ I₂ (n.val+1))
    (live : P (History.graphSequence (closingLayerHistory (carriedBoundarySources P u word ∘ Subtype.val) (n.val+1) root)))
    (exit : closingFirstExit (fun m s => boundary m (mapClosingLayer Subtype.val m s)) (n.val+1) root = true) :
    ∀ k, InputConnected P (closingLayerHistory (carriedBoundarySources P u word ∘ Subtype.val) (n.val+1) root) k →
      ∃ s : ClosingLayer (ActiveClosingRoots active) I₁ I₂ (n.val+1),
        closingLayerHistory (carriedBoundarySources P u word ∘ Subtype.val) (n.val+1) s = k := by
  let past := carriedBoundarySources P u word
  let old := mapClosingLayer Subtype.val (n.val+1) root
  let h := closingLayerHistory past (n.val+1) old
  let L := List.length u + List.length word
  have depth := carriedBoundarySources_depth P u word
  have oldLive : P (History.graphSequence h) := by simpa only [closingLayerHistory_map] using live
  have oldExit : closingFirstExit boundary (n.val+1) old = true := by
    simpa only [closingFirstExit,closingActive_map] using exit
  have phase := live_carried_first_exit_phase P closed d recent u word liveU startU active activity boundary flags n old oldLive
    (activeClosingLayer_root_alive active (n.val+1) root) oldExit
  intro k conn
  have oldConn : InputConnected P h k := by simpa only [closingLayerHistory_map] using conn
  obtain ⟨s,eq⟩ := scheduled_boundary_coverage P closed d recent u word (n.val+1) (by omega) (by omega)
    scheduled old oldLive phase k oldConn
  have kLive := inputConnected_live P oldLive oldConn
  have sourceLive : P (History.graphSequence (past (closingLayerRoot (n.val+1) s))) := by
    rw [← closingLayerHistory_take_source past L depth (n.val+1) s,eq]
    exact live_history_take P closed _ kLive L
  have alive : active (closingLayerRoot (n.val+1) s) = true := by
    apply (activity _ sourceLive).mpr
    intro m lo hi
    rw [← closingLayerHistory_take_before_source past L depth (n.val+1) s m hi,eq,
      ← leaderBoundary_history_component P closed d recent oldLive oldConn m]
    apply phase.no_boundary m lo
    rw [closingLayerHistory_length past L depth]
    omega
  obtain ⟨t,teq⟩ := activeClosingLayer_preimage active (n.val+1) s alive
  exact ⟨t,by rw [closingLayerHistory_map,teq,eq]⟩

end Coverage
end Characterisation
