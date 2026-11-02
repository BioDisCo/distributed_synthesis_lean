/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.CanonicalClosingSchedule

/-! Scheduled live first exits of the carried active family cover their
complete target component. Unlike the arbitrary-window theorem, this result
has no separate target-coverage hypothesis. -/
namespace Characterisation
open DistributedSynthesis

section Coverage
variable {I₁ I₂ : Type}
variable (P : List Graph → Prop) (closed : PrefixClosed P) (d : Nat)
variable (recent : ∀ g, P g → ∃ p, RecentOther P d g p)
variable (u word : EnvHistory I₁ I₂) (liveU : P (History.graphSequence u))
variable (startU : leaderBoundary P d u = true)
variable (active : InputHistoryComponent P u → Bool)
variable (exactActivity : SourceActivityExact P d (List.length u) (List.length u + List.length word)
  (carriedBoundarySources P u word) active)
variable (boundary : ClosingFlagTable (InputHistoryComponent P u) I₁ I₂ (d+1))
variable (exactFlags : ∀ m s, boundary m s =
  leaderBoundary P d (closingLayerHistory (carriedBoundarySources P u word) m.val s))

include closed recent liveU startU in
theorem carriedBoundarySources_start (s : InputHistoryComponent P u) :
    leaderBoundary P d ((carriedBoundarySources P u word s).take (List.length u)) = true := by
  have len := inputConnected_length P s.property
  have flags := leaderBoundary_component P closed d u s.val
    (componentLeader_correct P d _ (recent _ liveU)) s.property
  change leaderBoundary P d ((s.val ++ word).take (List.length u)) = true
  rw [len,List.take_left,← flags,startU]

include closed recent liveU startU exactActivity exactFlags in
/-- The carried activity bit and first-exit mask recover the original
consecutive-boundary interval, including its final physical output. -/
theorem carried_active_first_exit_phase (n : Fin (d+1))
    (root : ClosingLayer (InputHistoryComponent P u) I₁ I₂ (n.val+1))
    (alive : active (closingLayerRoot (n.val+1) root) = true)
    (exit : closingFirstExit (closingFlagAt boundary) (n.val+1) root = true) :
    ConsecutiveLeaderBoundaries P d
      (closingLayerHistory (carriedBoundarySources P u word) (n.val+1) root) (List.length u) := by
  have flags := closingFlagAt_exact boundary
    (fun m s => leaderBoundary P d (closingLayerHistory (carriedBoundarySources P u word) m s)) exactFlags
  have exitParts := exit
  simp only [closingFirstExit,Bool.and_eq_true] at exitParts
  have interval := activeClosingLayer_phase_interval P d (List.length u)
    (List.length u + List.length word) (by omega) (carriedBoundarySources P u word)
    (carriedBoundarySources_depth P u word) active exactActivity
    (fun s => Or.inr (carriedBoundarySources_start P closed d recent u word liveU startU s))
    (closingFlagAt boundary) (d+1) flags n.val (by omega) root alive exitParts.1
  refine ⟨interval.start_lt,?_,?_,interval.no_boundary⟩
  · rw [closingLayerHistory_take_before_source _ _ (carriedBoundarySources_depth P u word)
      (n.val+1) root (List.length u) (by omega)]
    exact carriedBoundarySources_start P closed d recent u word liveU startU _
  · exact (flags (n.val+1) (by omega) root).symm.trans exitParts.2

include closed recent liveU startU exactActivity exactFlags in
/-- Every scheduled live exit has complete coverage after removal of roots
that handed over earlier. The original family is the full boundary component. -/
theorem scheduled_active_root_coverage (n : Fin (d+1))
    (scheduled : closingWindowScheduled (decide (List.length word = 0)) (d+1) (n.val+1) = true)
    (root : ClosingLayer (ActiveClosingRoots active) I₁ I₂ (n.val+1))
    (live : P (History.graphSequence
      (closingLayerHistory (carriedBoundarySources P u word ∘ Subtype.val) (n.val+1) root)))
    (exit : closingFirstExit (closingFlagAt (restrictClosingFlags Subtype.val boundary)) (n.val+1) root = true) :
    ∀ k, InputConnected P
        (closingLayerHistory (carriedBoundarySources P u word ∘ Subtype.val) (n.val+1) root) k →
      ∃ s : ClosingLayer (ActiveClosingRoots active) I₁ I₂ (n.val+1),
        closingLayerHistory (carriedBoundarySources P u word ∘ Subtype.val) (n.val+1) s = k := by
  have oldExit : closingFirstExit (closingFlagAt boundary) (n.val+1)
      (mapClosingLayer Subtype.val (n.val+1) root) = true := by
    simpa only [closingFirstExit_restrict] using exit
  have phase := carried_active_first_exit_phase P closed d recent u word liveU startU active exactActivity
    boundary exactFlags n _ (activeClosingLayer_root_alive active (n.val+1) root) oldExit
  have oldLive : P (History.graphSequence (closingLayerHistory (carriedBoundarySources P u word)
      (n.val+1) (mapClosingLayer Subtype.val (n.val+1) root))) := by
    simpa only [closingLayerHistory_map] using live
  apply activeClosingLayer_component_coverage P closed d recent (carriedBoundarySources P u word)
    (List.length u) (List.length u + List.length word) (carriedBoundarySources_depth P u word)
    active exactActivity (n.val+1) root live
  intro k conn
  have oldConn : InputConnected P (closingLayerHistory (carriedBoundarySources P u word)
      (n.val+1) (mapClosingLayer Subtype.val (n.val+1) root)) k := by
    simpa only [closingLayerHistory_map] using conn
  exact scheduled_boundary_coverage P closed d recent u word (n.val+1) (by omega) (by omega)
    scheduled _ oldLive phase k oldConn

end Coverage

/-- Every actual handover has a surviving canonical representation, and
so does every history in its complete target component. This also rules out
an empty active source family at a handover that really occurs. -/
theorem canonical_boundary_active_coverage {I₁ I₂ : Type}
    (P : List Graph → Prop) (closed : PrefixClosed P) (d : Nat)
    (recent : ∀ g, P g → ∃ p, RecentOther P d g p)
    (h : EnvHistory I₁ I₂) (live : P (History.graphSequence h))
    (a : Nat) (phase : ConsecutiveLeaderBoundaries P d h a)
    (active : InputHistoryComponent P (h.take a) → Bool)
    (exactActivity : SourceActivityExact P d a (phaseClosingCut d h a)
      (boundaryPhaseSources P d h a) active) :
    ∀ k, InputConnected P h k →
      ∃ s : ClosingLayer (ActiveClosingRoots active) I₁ I₂ (List.length h-phaseClosingCut d h a),
        closingLayerHistory (boundaryPhaseSources P d h a ∘ Subtype.val)
          (List.length h-phaseClosingCut d h a) s = k := by
  intro k conn
  obtain ⟨s,eq⟩ := boundaryRoots_closing_coverage P closed d recent live conn a phase
  have alive : active (closingLayerRoot (List.length h-phaseClosingCut d h a) s) = true := by
    apply (exactActivity _).mpr
    intro m lower upper
    rw [← closingLayerHistory_take_before_source (boundaryPhaseSources P d h a)
      (phaseClosingCut d h a) (boundaryPhaseSources_depth P d h a phase)
      (List.length h-phaseClosingCut d h a) s m upper,eq,
      ← leaderBoundary_history_component P closed d recent live conn m]
    exact phase.no_boundary m lower (lt_of_le_of_lt upper (phaseClosingCut_bounds P d h a phase).2.1)
  obtain ⟨t,teq⟩ := activeClosingLayer_preimage active _ s alive
  exact ⟨t,by rw [closingLayerHistory_map,teq,eq]⟩


/-- No actual handover is lost by ignoring short exits of later windows.
Its canonical window contains a surviving first exit at the original depth. -/
theorem every_boundary_has_scheduled_active_exit {I₁ I₂ : Type}
    (P : List Graph → Prop) (closed : PrefixClosed P) (d : Nat)
    (recent : ∀ g, P g → ∃ p, RecentOther P d g p)
    (h : EnvHistory I₁ I₂) (live : P (History.graphSequence h))
    (a : Nat) (phase : ConsecutiveLeaderBoundaries P d h a)
    (active : InputHistoryComponent P (h.take a) → Bool)
    (exactActivity : SourceActivityExact P d a (phaseClosingCut d h a)
      (boundaryPhaseSources P d h a) active) :
    let n := List.length h-phaseClosingCut d h a
    let past := boundaryPhaseSources P d h a ∘ (Subtype.val : ActiveClosingRoots active → _)
    0 < n ∧ n ≤ d+1 ∧
    closingWindowScheduled (decide (List.length (boundaryPhaseWord d h a) = 0)) (d+1) n = true ∧
    ∃ root : ClosingLayer (ActiveClosingRoots active) I₁ I₂ n,
      closingLayerHistory past n root = h ∧
      closingFirstExit (fun m s => leaderBoundary P d (closingLayerHistory past m s)) n root = true := by
  dsimp only
  have bounds := phaseClosingCut_bounds P d h a phase
  have scheduled : closingWindowScheduled (decide (List.length (boundaryPhaseWord d h a) = 0))
      (d+1) (List.length h-phaseClosingCut d h a) = true := by
    simp only [closingWindowScheduled,Bool.or_eq_true,decide_eq_true_eq,
      boundaryPhaseWord,List.length_drop,List.length_take,min_eq_left (Nat.le_of_lt bounds.2.1)]
    unfold phaseClosingCut
    omega
  refine ⟨by omega,bounds.2.2,scheduled,?_⟩
  obtain ⟨root,eq⟩ := canonical_boundary_active_coverage P closed d recent h live a phase active exactActivity
    h Relation.ReflTransGen.refl
  refine ⟨root,eq,?_⟩
  let past := boundaryPhaseSources P d h a ∘ (Subtype.val : ActiveClosingRoots active → _)
  have depth : ∀ s, List.length (past s) = phaseClosingCut d h a :=
    fun s => boundaryPhaseSources_depth P d h a phase s.val
  generalize hn : List.length h-phaseClosingCut d h a = n at root eq ⊢
  cases n with
  | zero => omega
  | succ n =>
    apply (closingFirstExit_exact P d past (phaseClosingCut d h a) depth
      (fun m s => leaderBoundary P d (closingLayerHistory past m s)) (d+1)
      (fun _ _ _ => rfl) n (by omega) root).mpr
    constructor
    · intro m lower upper
      rw [eq]
      exact phase.no_boundary m (by omega) (by omega)
    · rw [eq]
      exact phase.end_boundary

end Characterisation
