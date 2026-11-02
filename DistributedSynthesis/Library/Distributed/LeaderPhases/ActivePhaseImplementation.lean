/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.ActiveRootCoverage
import DistributedSynthesis.Library.Distributed.LeaderPhases.ActiveRootMonitor

/-! Persistent source activity and the bounded active scan identify exactly
the portion implemented by the original phase controller. This connects
active-root restriction to the proved semantic phase composition. -/
namespace Characterisation
open DistributedSynthesis

/-- Source activity covers all rounds through the source cut; the closing
mask covers the remaining rounds strictly before the current output. -/
theorem activeClosingLayer_phase_interval {H I₁ I₂ : Type}
    (P : List Graph → Prop) (d a L : Nat) (before : a ≤ L)
    (past : H → EnvHistory I₁ I₂) (depth : ∀ h, List.length (past h) = L)
    (active : H → Bool) (exactActivity : SourceActivityExact P d a L past active)
    (start : ∀ h, a = 0 ∨ leaderBoundary P d ((past h).take a) = true)
    (boundary : (n : Nat) → ClosingLayer H I₁ I₂ n → Bool)
    (D : Nat) (exactFlags : ∀ n, n ≤ D → ∀ s,
      boundary n s = leaderBoundary P d (closingLayerHistory past n s))
    (n : Nat) (bound : n+1 ≤ D) (s : ClosingLayer H I₁ I₂ (n+1))
    (alive : active (closingLayerRoot (n+1) s) = true)
    (scan : closingActive boundary (n+1) s = true) :
    LeaderPhaseInterval P d (closingLayerHistory past (n+1) s) a := by
  have old := (exactActivity _).mp alive
  have later := (closingActive_exact P d past L depth boundary D exactFlags (n+1) bound s).mp scan
  refine ⟨by rw [closingLayerHistory_length past L depth]; omega,?_,?_⟩
  · simpa only [closingLayerHistory_take_before_source past L depth (n+1) s a before] using
      start (closingLayerRoot (n+1) s)
  · intro m lower upper
    rw [closingLayerHistory_length past L depth] at upper
    by_cases early : m ≤ L
    · rw [closingLayerHistory_take_before_source past L depth (n+1) s m early]
      exact old m lower early
    · exact later m (by omega) upper

/-- The original phase policy is implemented on every live active scenario
of the restricted checker. This derives the earlier implementation premise
from semantic composition and the truthful carried activity bits. -/
theorem active_root_policy_implemented {H I₁ I₂ O₁ O₂ : Type} {D : Nat}
    (P : List Graph → Prop) (closed : PrefixClosed P) (d a L : Nat) (before : a ≤ L)
    (past : H → EnvHistory I₁ I₂) (depth : ∀ h, List.length (past h) = L)
    (active : H → Bool) (exactActivity : SourceActivityExact P d a L past active)
    (start : ∀ h, a = 0 ∨ leaderBoundary P d ((past h).take a) = true)
    (C : Set (EnvHistory I₁ I₂)) (origins : ∀ h, inputComponentSet P ((past h).take a) = C)
    (boundary : ClosingFlagTable H I₁ I₂ D)
    (exactFlags : ∀ n s, boundary n s = leaderBoundary P d (closingLayerHistory past n.val s))
    (controllers : LeaderPhaseOrigin I₁ I₂ → StrategyPair I₁ I₂ O₁ O₂)
    (σ : StrategyPair I₁ I₂ O₁ O₂) (impl : ImplementsPhaseFamily P d controllers σ)
    (out : ClosingPolicy H I₁ I₂ O₁ O₂ D)
    (policy : ∀ t s, out t s =
      ((controllers (a,C)).one (currentView .one (closingLayerHistory past (t.val+1) s)),
       (controllers (a,C)).two (currentView .two (closingLayerHistory past (t.val+1) s)))) :
    ∀ t s, LiveClosingActive P (past ∘ (Subtype.val : ActiveClosingRoots active → H))
      (closingFlagAt (restrictClosingFlags Subtype.val boundary)) (t.val+1) s →
      restrictClosingPolicy Subtype.val out t s =
        (σ.one (currentView .one (closingLayerHistory (past ∘ Subtype.val) (t.val+1) s)),
         σ.two (currentView .two (closingLayerHistory (past ∘ Subtype.val) (t.val+1) s))) := by
  intro t s valid
  let old := mapClosingLayer Subtype.val (t.val+1) s
  have alive := activeClosingLayer_root_alive active (t.val+1) s
  have scan : closingActive (closingFlagAt boundary) (t.val+1) old = true := by
    simpa only [closingActive_restrict] using valid.1
  have live : P (History.graphSequence (closingLayerHistory past (t.val+1) old)) := by
    simpa only [closingLayerHistory_map] using valid.2
  have phase := activeClosingLayer_phase_interval P d a L before past depth active exactActivity start
    (closingFlagAt boundary) D
    (closingFlagAt_exact boundary (fun n s => leaderBoundary P d (closingLayerHistory past n s)) exactFlags)
    t.val (by omega) old alive scan
  have correct := phase_implementation_on_interval P closed d controllers σ impl
    (closingLayerHistory past (t.val+1) old) live a phase
    (List.length (closingLayerHistory past (t.val+1) old)) phase.start_lt (Nat.le_refl _)
  simp only [List.take_length,closingLayerHistory_take_before_source past L depth (t.val+1) old a before,
    origins] at correct
  simpa only [restrictClosingPolicy,closingLayerHistory_map] using (policy t old).trans correct.symm

end Characterisation
