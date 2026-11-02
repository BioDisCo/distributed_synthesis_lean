/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.RootActivityMemory

/-! Monitor states are updated together with root activity. Only live active
roots need agree with the composed strategy; hypothetical states on roots
that already handed over are never used by a later active-root scan. -/
namespace Characterisation
open DistributedSynthesis

def rootMonitorRun {H I₁ I₂ O₁ O₂ Q : Type}
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (initial : H → Q)
    (round : Nat → H → RoundRecord I₁ I₂ Graph Unit Unit) (output : Nat → H → O₁ × O₂) : Nat → H → Q
  | 0 => initial
  | n+1 => fun h => step (rootMonitorRun step initial round output n h)
      ((round n h).inputOne,(round n h).inputTwo,(round n h).graph) (output n h)

/-- One finite state contains both the persistent activity bits and the
monitor vector. This is an instance of the existing phase-memory update. -/
theorem rootActivityAndLabels_phaseMemory {H I₁ I₂ O₁ O₂ Q : Type}
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (initial : H → Q)
    (boundary : Nat → H → Bool) (round : Nat → H → RoundRecord I₁ I₂ Graph Unit Unit)
    (output : Nat → H → O₁ × O₂) (n : Nat) :
    phaseMemoryRun ((fun _ : H => true),initial)
      (fun state (letter : (H → Bool) × (H → RoundRecord I₁ I₂ Graph Unit Unit) × (H → O₁ × O₂)) =>
        (rootActivityNext state.1 letter.1,
         fun h => step (state.2 h) ((letter.2.1 h).inputOne,(letter.2.1 h).inputTwo,(letter.2.1 h).graph)
           (letter.2.2 h)))
      (fun i => (boundary i,round i,output i)) n =
      (rootActivityRun boundary n,rootMonitorRun step initial round output n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [phaseMemoryRun,ih,rootActivityRun,rootMonitorRun]

section Exact
variable {H I₁ I₂ O₁ O₂ Q : Type}
variable (P : List Graph → Prop) (closed : PrefixClosed P)
variable (σ : StrategyPair I₁ I₂ O₁ O₂)
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (q₀ : Q) (initial : H → Q)
variable (history : Nat → H → EnvHistory I₁ I₂)
variable (round : Nat → H → RoundRecord I₁ I₂ Graph Unit Unit)
variable (next : ∀ n h, history (n+1) h = history n h ++ [round n h])
variable (boundary : Nat → H → Bool) (output : Nat → H → O₁ × O₂)
variable (start : ∀ h, P (History.graphSequence (history 0 h)) →
  initial h = strategyHistoryLabel σ step q₀ (history 0 h))
variable (implements : ∀ n h, rootActivityRun boundary n h = true →
  P (History.graphSequence (history (n+1) h)) → output n h =
    (σ.one (currentView .one (history (n+1) h)),σ.two (currentView .two (history (n+1) h))))

include closed next in
theorem rootHistory_live_parent (n : Nat) (h : H)
    (live : P (History.graphSequence (history (n+1) h))) :
    P (History.graphSequence (history n h)) := by
  apply closed _ [(round n h).graph]
  simpa only [next,History.graphSequence,List.map_append,List.map_cons,List.map_nil] using live

include closed next start implements in
/-- At every new scan source, labels on the surviving live roots are the
actual composed strategy's monitor states. No claim is made for dead roots. -/
theorem rootMonitorRun_active_exact (n : Nat) (h : H)
    (active : rootActivityRun boundary n h = true)
    (live : P (History.graphSequence (history n h))) :
    rootMonitorRun step initial round output n h = strategyHistoryLabel σ step q₀ (history n h) := by
  induction n with
  | zero => exact start h live
  | succ n ih =>
    have previous : rootActivityRun boundary n h = true := by
      apply (rootActivityRun_exact boundary n h).mpr
      exact fun i hi => (rootActivityRun_exact boundary (n+1) h).mp active i (by omega)
    have oldLive := rootHistory_live_parent P closed history round next n h live
    simp only [rootMonitorRun]
    rw [ih previous oldLive,implements n h previous live,next n h,strategyHistoryLabel_append]

include closed next start implements in
/-- The label at the handing-over output is also exact, even though that
output clears the activity bit. Only later hypothetical labels are discarded. -/
theorem rootMonitorRun_exit_exact (n : Nat) (h : H)
    (active : rootActivityRun boundary n h = true)
    (live : P (History.graphSequence (history (n+1) h))) :
    rootMonitorRun step initial round output (n+1) h = strategyHistoryLabel σ step q₀ (history (n+1) h) := by
  have old := rootMonitorRun_active_exact P closed σ step q₀ initial history round next boundary output
    start implements n h active (rootHistory_live_parent P closed history round next n h live)
  simp only [rootMonitorRun]
  rw [old,implements n h active live,next n h,strategyHistoryLabel_append]

end Exact
end Characterisation
