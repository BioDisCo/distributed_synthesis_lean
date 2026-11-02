/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.LiveScheduledCoverage

/-! Reindex the existing canonical coverage proof instead of adding a
coverage assumption to numbered local moves. Physical histories and complete
successor components remain those of the original boundary family. -/
namespace Characterisation
open DistributedSynthesis

def closingLayerEquiv {H J I₁ I₂ : Type} (e : H ≃ J) (n : Nat) :
    ClosingLayer H I₁ I₂ n ≃ ClosingLayer J I₁ I₂ n where
  toFun := mapClosingLayer e n
  invFun := mapClosingLayer e.symm n
  left_inv := by
    intro s
    induction n with
    | zero => exact e.symm_apply_apply s
    | succ n ih => exact Prod.ext (ih s.1) rfl
  right_inv := by
    intro s
    induction n with
    | zero => exact e.apply_symm_apply s
    | succ n ih => exact Prod.ext (ih s.1) rfl

theorem closingFirstExit_map {H J I₁ I₂ : Type} (f : H → J)
    (boundary : (n : Nat) → ClosingLayer J I₁ I₂ n → Bool)
    (n : Nat) (s : ClosingLayer H I₁ I₂ n) :
    closingFirstExit (fun m t => boundary m (mapClosingLayer f m t)) n s =
      closingFirstExit boundary n (mapClosingLayer f n s) := by
  cases n with
  | zero => rfl
  | succ n => simp only [closingFirstExit,closingActive_map]

section Numbering
variable {H I₁ I₂ : Type}
variable (P : List Graph → Prop) (closed : PrefixClosed P) (d : Nat)
variable (recent : ∀ g, P g → ∃ p, RecentOther P d g p)
variable (u word : EnvHistory I₁ I₂) (e : H ≃ InputHistoryComponent P u)
variable (liveU : P (History.graphSequence u)) (startU : leaderBoundary P d u = true)

include closed recent in
theorem numbered_scheduled_boundary_coverage
    (n : Nat) (positive : 0 < n) (bounded : n ≤ d+1)
    (scheduled : closingWindowScheduled (decide (List.length word = 0)) (d+1) n = true)
    (root : ClosingLayer H I₁ I₂ n)
    (live : P (History.graphSequence (closingLayerHistory (carriedBoundarySources P u word ∘ e) n root)))
    (phase : ConsecutiveLeaderBoundaries P d
      (closingLayerHistory (carriedBoundarySources P u word ∘ e) n root) (List.length u)) :
    ∀ k, InputConnected P (closingLayerHistory (carriedBoundarySources P u word ∘ e) n root) k →
      ∃ s, closingLayerHistory (carriedBoundarySources P u word ∘ e) n s = k := by
  intro k conn
  have covers := scheduled_boundary_coverage P closed d recent u word n positive bounded scheduled
    (mapClosingLayer e n root)
    (by simpa only [closingLayerHistory_map] using live)
    (by simpa only [closingLayerHistory_map] using phase)
    k (by simpa only [closingLayerHistory_map] using conn)
  obtain ⟨s,eq⟩ := covers
  obtain ⟨t,rfl⟩ := (closingLayerEquiv (I₁:=I₁) (I₂:=I₂) e n).surjective s
  exact ⟨t,by simpa only [closingLayerEquiv,Equiv.coe_fn_mk,closingLayerHistory_map] using eq⟩

variable (active : H → Bool)
variable (activity : SourceActivityOnLive P d (List.length u) (List.length u + List.length word)
  (carriedBoundarySources P u word ∘ e) active)
variable (boundary : (n : Nat) → ClosingLayer H I₁ I₂ n → Bool)
variable (flags : ∀ n, 0 < n → n ≤ d+1 → ∀ s,
  P (History.graphSequence (closingLayerHistory (carriedBoundarySources P u word ∘ e) n s)) →
  boundary n s = leaderBoundary P d (closingLayerHistory (carriedBoundarySources P u word ∘ e) n s))

include closed recent liveU startU activity flags in
theorem numbered_live_first_exit_phase (n : Fin (d+1)) (root : ClosingLayer H I₁ I₂ (n.val+1))
    (live : P (History.graphSequence (closingLayerHistory (carriedBoundarySources P u word ∘ e) (n.val+1) root)))
    (alive : active (closingLayerRoot (n.val+1) root) = true)
    (exit : closingFirstExit boundary (n.val+1) root = true) :
    ConsecutiveLeaderBoundaries P d
      (closingLayerHistory (carriedBoundarySources P u word ∘ e) (n.val+1) root) (List.length u) := by
  let past := carriedBoundarySources P u word
  let oldActive := fun h => active (e.symm h)
  let oldBoundary := fun m s => leaderBoundary P d (closingLayerHistory past m s)
  have oldActivity : SourceActivityOnLive P d (List.length u) (List.length u + List.length word) past oldActive := by
    intro h liveH
    simpa only [Function.comp_apply,Equiv.apply_symm_apply] using
      activity (e.symm h) (by simpa only [Function.comp_apply,Equiv.apply_symm_apply] using liveH)
  have agree := closingFirstExit_congr_on_live P closed (past ∘ e) boundary
    (fun m s => leaderBoundary P d (closingLayerHistory (past ∘ e) m s)) (d+1) flags
    (n.val+1) (by omega) root live
  have mapped : closingFirstExit oldBoundary (n.val+1) (mapClosingLayer e (n.val+1) root) = true := by
    rw [← closingFirstExit_map e oldBoundary]
    simpa only [oldBoundary,closingLayerHistory_map] using agree.symm.trans exit
  have result := live_carried_first_exit_phase P closed d recent u word liveU startU oldActive oldActivity
    oldBoundary (fun _ _ _ _ _ => rfl) n (mapClosingLayer e (n.val+1) root)
    (by simpa only [closingLayerHistory_map] using live)
    (by simpa only [oldActive,closingLayerRoot_map,Equiv.symm_apply_apply] using alive) mapped
  simpa only [closingLayerHistory_map] using result

include closed recent liveU startU activity flags in
/-- The canonical numbered scan covers every target history after inactive
roots have been removed. No numbered target-coverage hypothesis is needed. -/
theorem numbered_scheduled_active_coverage (n : Fin (d+1))
    (scheduled : closingWindowScheduled (decide (List.length word = 0)) (d+1) (n.val+1) = true)
    (root : ClosingLayer (ActiveClosingRoots active) I₁ I₂ (n.val+1))
    (live : P (History.graphSequence
      (closingLayerHistory ((carriedBoundarySources P u word ∘ e) ∘ Subtype.val) (n.val+1) root)))
    (exit : closingFirstExit (fun m s => boundary m (mapClosingLayer Subtype.val m s)) (n.val+1) root = true) :
    ∀ k, InputConnected P
      (closingLayerHistory ((carriedBoundarySources P u word ∘ e) ∘ Subtype.val) (n.val+1) root) k →
      ∃ s : ClosingLayer (ActiveClosingRoots active) I₁ I₂ (n.val+1),
        closingLayerHistory ((carriedBoundarySources P u word ∘ e) ∘ Subtype.val) (n.val+1) s = k := by
  let past := carriedBoundarySources P u word ∘ e
  let old := mapClosingLayer Subtype.val (n.val+1) root
  let h := closingLayerHistory past (n.val+1) old
  let L := List.length u + List.length word
  have depth : ∀ s, List.length (past s) = L := fun s => carriedBoundarySources_depth P u word (e s)
  have oldLive : P (History.graphSequence h) := by simpa only [h,past,old,closingLayerHistory_map] using live
  have oldExit : closingFirstExit boundary (n.val+1) old = true := by
    simpa only [closingFirstExit_map] using exit
  have phase := numbered_live_first_exit_phase P closed d recent u word e liveU startU active activity boundary flags
    n old oldLive (activeClosingLayer_root_alive active (n.val+1) root) oldExit
  intro k conn
  have oldConn : InputConnected P h k := by simpa only [h,past,old,closingLayerHistory_map] using conn
  obtain ⟨s,eq⟩ := numbered_scheduled_boundary_coverage P closed d recent u word e (n.val+1)
    (by omega) (by omega) scheduled old oldLive phase k oldConn
  have sourceLive : P (History.graphSequence (past (closingLayerRoot (n.val+1) s))) := by
    rw [← closingLayerHistory_take_source past L depth (n.val+1) s,eq]
    exact live_history_take P closed _ (inputConnected_live P oldLive oldConn) L
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

end Numbering
end Characterisation
