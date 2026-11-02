/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.PhaseMonitorComposition
import DistributedSynthesis.Formalizations.Lemma.LemEpochReplayStep

/-! Compute phase priority minima from the selected controllers and the
carried actual monitor states. Their parity equals that of the composed
physical run. The proof reuses the existing block-minimum parity theorem. -/
namespace Characterisation
open DistributedSynthesis

section Slices
variable {I₁ I₂ : Type}
variable (history : Nat → EnvHistory I₁ I₂)
variable (depth : ∀ n, List.length (history n) = n)
variable (prefixes : ∀ m n, m ≤ n → (history n).take m = history m)
variable (cuts : Nat → Nat) (mono : StrictMono cuts)

def phaseSlice (n : Nat) : EnvHistory I₁ I₂ := (history (cuts (n+1))).drop (cuts n)

include prefixes mono in
theorem phaseSlice_next (n : Nat) :
    history (cuts (n+1)) = history (cuts n) ++ phaseSlice history cuts n := by
  rw [← prefixes (cuts n) (cuts (n+1)) (mono.monotone (by omega))]
  exact (List.take_append_drop _ _).symm

include depth in
theorem phaseSlice_length (n : Nat) :
    List.length (phaseSlice history cuts n) = cuts (n+1) - cuts n := by
  simp only [phaseSlice,List.length_drop,depth]

include prefixes mono in
theorem phaseSlice_prefix (n i : Nat) (bound : cuts n + i ≤ cuts (n+1)) :
    history (cuts n) ++ (phaseSlice history cuts n).take i = history (cuts n+i) := by
  rw [← prefixes (cuts n+i) (cuts (n+1)) bound,List.take_add]
  rw [prefixes (cuts n) (cuts (n+1)) (mono.monotone (by omega))]
  rfl

include depth prefixes in
theorem leaderPhaseCuts_intervals (P : List Graph → Prop) (d : Nat)
    (phases : LeaderPhaseCuts P d history cuts) (n : Nat) :
    LeaderPhaseInterval P d (history (cuts (n+1))) (List.length (history (cuts n))) := by
  have strict := phases.2.1 (show n < n+1 by omega)
  simp only [depth]
  refine ⟨by rw [depth]; exact strict,?_,?_⟩
  · rw [prefixes _ _ (Nat.le_of_lt strict)]
    cases n with
    | zero => exact Or.inl phases.1
    | succ n => exact Or.inr (phases.2.2 n).1
  · intro t lower upper
    rw [depth] at upper
    rw [prefixes _ _ (Nat.le_of_lt upper)]
    exact (phases.2.2 n).2 t lower upper

end Slices

section Parity
variable {I₁ I₂ O₁ O₂ Q : Type}
variable (P : List Graph → Prop) (closed : PrefixClosed P) (d : Nat)
variable (controllers : LeaderPhaseOrigin I₁ I₂ → StrategyPair I₁ I₂ O₁ O₂)
variable (σ : StrategyPair I₁ I₂ O₁ O₂) (impl : ImplementsPhaseFamily P d controllers σ)
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (q₀ : Q)
variable (history : Nat → EnvHistory I₁ I₂)
variable (depth : ∀ n, List.length (history n) = n)
variable (prefixes : ∀ m n, m ≤ n → (history n).take m = history m)
variable (live : ∀ n, P (History.graphSequence (history n)))
variable (cuts : Nat → Nat) (phases : LeaderPhaseCuts P d history cuts)

/-- Priority after each actual output of the phase, starting from the
carried boundary state. The argument i remains a physical round offset. -/
def composedPhasePriority (priority : Q → Nat) (n i : Nat) : Nat :=
  let root := history (cuts n)
  let word := phaseSlice history cuts n
  let incoming := phaseBoundaryLabels P controllers step q₀
    (fun k => history (cuts k)) (phaseSlice history cuts) n
  priority (strategyContinuationLabel
    (controllers (List.length root,inputComponentSet P root)) step incoming root (word.take (i+1)))

include closed impl depth prefixes live phases in
theorem composedPhasePriority_exact (priority : Q → Nat) (n i : Nat)
    (within : i < cuts (n+1) - cuts n) :
    composedPhasePriority P controllers step q₀ history cuts priority n i =
      priority (strategyHistoryLabel σ step q₀ (history (cuts n+i+1))) := by
  have strict := phases.2.1 (show n < n+1 by omega)
  have bounds : cuts n + (i+1) ≤ cuts (n+1) := by omega
  have slice := phaseSlice_prefix history prefixes cuts phases.2.1 n (i+1) bounds
  have endpoint := leaderPhaseCuts_intervals history depth prefixes cuts P d phases n
  have shorter := leaderPhaseInterval_take P d (history (cuts (n+1)))
    (List.length (history (cuts n))) endpoint (cuts n+(i+1)) (by rw [depth]; omega)
    (by rw [depth]; exact bounds)
  rw [prefixes _ _ bounds,← slice] at shorter
  have initial : history (cuts 0) = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [depth,phases.1]
  have labels := phase_boundary_labels_exact P closed d controllers σ impl step q₀
    (fun k => history (cuts k)) (phaseSlice history cuts) initial
    (phaseSlice_next history prefixes cuts phases.2.1)
    (fun k => live (cuts (k+1))) (leaderPhaseCuts_intervals history depth prefixes cuts P d phases) n
  have replay := phase_monitor_replay P closed d controllers σ impl step q₀
    (history (cuts n)) ((phaseSlice history cuts n).take (i+1))
    (by rw [slice]; exact live _) shorter
  simp only [composedPhasePriority]
  rw [labels,← replay,slice]
  simp only [Nat.add_assoc]

/-- The computed minimum includes every output through the closing boundary.
Its state is carried from the actual previous phase, not reset to q₀. -/
def composedPhaseMinimum (priority : Q → Nat) (n : Nat) : Nat :=
  rangeMin (composedPhasePriority P controllers step q₀ history cuts priority n) 0
    (cuts (n+1)-cuts n-1)

include closed impl depth prefixes live phases in
theorem composedPhaseMinimum_exact (priority : Q → Nat) (n : Nat) :
    composedPhaseMinimum P controllers step q₀ history cuts priority n =
      cutBlockMin (fun t => priority (strategyHistoryLabel σ step q₀ (history (t+1)))) cuts n := by
  unfold composedPhaseMinimum cutBlockMin
  apply rangeMin_congr
  intro i bound
  have strict := phases.2.1 (show n < n+1 by omega)
  simpa only [Nat.zero_add] using composedPhasePriority_exact P closed d controllers σ impl
    step q₀ history depth prefixes live cuts phases priority n i (by omega)

include closed impl depth prefixes live phases in
/-- Exact global parity accounting for the composed strategy on runs with
infinitely many phases. This equivalence does not assert that either side
is winning; establishing winning finite-game choices remains separate. -/
theorem composed_phases_parity_iff (priority : Q → Nat) :
    NatSeqMinEvenParity (composedPhaseMinimum P controllers step q₀ history cuts priority) ↔
      NatSeqMinEvenParity (fun t => priority (strategyHistoryLabel σ step q₀ (history (t+1)))) := by
  have minima := funext (composedPhaseMinimum_exact P closed d controllers σ impl
    step q₀ history depth prefixes live cuts phases priority)
  rw [minima]
  exact natSeqMinEvenParity_cutBlockMin _ phases.2.1 phases.1

include closed impl depth prefixes live phases in
/-- The same composition preserves the implication from adversary acceptance
to objective acceptance. Both priority maps can use the product monitor state. -/
theorem composed_phases_guarded_parity_iff (adversary objective : Q → Nat) :
    (NatSeqMinEvenParity (composedPhaseMinimum P controllers step q₀ history cuts adversary) →
      NatSeqMinEvenParity (composedPhaseMinimum P controllers step q₀ history cuts objective)) ↔
    (NatSeqMinEvenParity (fun t => adversary (strategyHistoryLabel σ step q₀ (history (t+1)))) →
      NatSeqMinEvenParity (fun t => objective (strategyHistoryLabel σ step q₀ (history (t+1))))) := by
  rw [composed_phases_parity_iff P closed d controllers σ impl step q₀ history depth prefixes live cuts phases,
    composed_phases_parity_iff P closed d controllers σ impl step q₀ history depth prefixes live cuts phases]

/-- Priority stream of a final phase, continued from the actual state at
its last boundary. A phase without a later boundary keeps this controller. -/
def finalPhasePriority (priority : Q → Nat) (N i : Nat) : Nat :=
  priority (strategyContinuationLabel
    (controllers (List.length (history N),inputComponentSet P (history N))) step
    (strategyHistoryLabel σ step q₀ (history N)) (history N)
    ((history (N+i+1)).drop N))

include closed impl depth prefixes live in
theorem finalPhasePriority_exact (priority : Q → Nat) (N : Nat)
    (start : N = 0 ∨ leaderBoundary P d (history N) = true)
    (absent : ∀ n, N < n → leaderBoundary P d (history n) = false) (i : Nat) :
    finalPhasePriority P controllers σ step q₀ history priority N i =
      priority (strategyHistoryLabel σ step q₀ (history (N+i+1))) := by
  have split : history N ++ (history (N+i+1)).drop N = history (N+i+1) := by
    rw [← prefixes N (N+i+1) (by omega)]
    exact List.take_append_drop _ _
  have phase : LeaderPhaseInterval P d (history (N+i+1)) (List.length (history N)) := by
    simp only [depth]
    refine ⟨by rw [depth]; omega,?_,?_⟩
    · rwa [prefixes N (N+i+1) (by omega)]
    · intro n lower upper
      rw [depth] at upper
      rw [prefixes _ _ (Nat.le_of_lt upper)]
      exact absent n lower
  have replay := phase_monitor_replay P closed d controllers σ impl step q₀
    (history N) ((history (N+i+1)).drop N)
    (by rw [split]; exact live _) (by rw [split]; exact phase)
  simp only [finalPhasePriority,← replay,split]

include closed impl depth prefixes live in
/-- Finitely many boundaries are handled by the actual final controller's
infinite suffix. Finite earlier phases do not affect parity. -/
theorem final_phase_parity_iff (priority : Q → Nat) (N : Nat)
    (start : N = 0 ∨ leaderBoundary P d (history N) = true)
    (absent : ∀ n, N < n → leaderBoundary P d (history n) = false) :
    NatSeqMinEvenParity (finalPhasePriority P controllers σ step q₀ history priority N) ↔
      NatSeqMinEvenParity (fun t => priority (strategyHistoryLabel σ step q₀ (history (t+1)))) := by
  have exactPriority := funext (finalPhasePriority_exact P closed d controllers σ impl
    step q₀ history depth prefixes live priority N start absent)
  rw [exactPriority]
  exact natSeqMinEvenParity_shift
    (fun t => priority (strategyHistoryLabel σ step q₀ (history (t+1)))) N

include depth prefixes in
/-- If boundaries do not occur arbitrarily late, a last boundary (or depth
zero) starts a final phase. This is an actual agreed start, not an arbitrary
time beyond the last boundary. -/
theorem finite_boundaries_last_phase
    (finite : ¬ InfinitelyManyLeaderBoundaries P d history) :
    ∃ N, (N = 0 ∨ leaderBoundary P d (history N) = true) ∧
      ∀ n, N < n → leaderBoundary P d (history n) = false := by
  classical
  unfold InfinitelyManyLeaderBoundaries at finite
  push Not at finite
  obtain ⟨B,beyond⟩ := finite
  let N := previousLeaderBoundary P d (history (B+1))
  have interval := previousLeaderBoundary_interval P d (history (B+1)) (by rw [depth]; omega)
  have start : N = 0 ∨ leaderBoundary P d (history N) = true := by
    have old := interval.start
    rw [prefixes N (B+1) (by have bound := interval.start_lt; rw [depth] at bound; omega)] at old
    exact old
  refine ⟨N,start,fun n lower => ?_⟩
  by_cases before : n < B+1
  · have no := interval.no_boundary n lower (by rw [depth]; exact before)
    rwa [prefixes n (B+1) (Nat.le_of_lt before)] at no
  · exact Bool.eq_false_iff.mpr (beyond n (by omega))

include closed impl depth prefixes live in
/-- Exhaustive parity accounting for one composed physical run. Infinite
switching uses the computed phase minima; finite switching uses the final
controller continued from its actual incoming monitor state. -/
theorem composed_parity_dichotomy (priority : Q → Nat) :
    (∃ c, LeaderPhaseCuts P d history c ∧
      (NatSeqMinEvenParity (composedPhaseMinimum P controllers step q₀ history c priority) ↔
        NatSeqMinEvenParity (fun t => priority (strategyHistoryLabel σ step q₀ (history (t+1)))))) ∨
    (∃ N, (N = 0 ∨ leaderBoundary P d (history N) = true) ∧
      (∀ n, N < n → leaderBoundary P d (history n) = false) ∧
      (NatSeqMinEvenParity (finalPhasePriority P controllers σ step q₀ history priority N) ↔
        NatSeqMinEvenParity (fun t => priority (strategyHistoryLabel σ step q₀ (history (t+1)))))) := by
  classical
  by_cases infinite : InfinitelyManyLeaderBoundaries P d history
  · obtain ⟨c,ph⟩ := exists_leader_phase_cuts P d history infinite
    exact Or.inl ⟨c,ph,composed_phases_parity_iff P closed d controllers σ impl
      step q₀ history depth prefixes live c ph priority⟩
  · obtain ⟨N,start,absent⟩ := finite_boundaries_last_phase P d history depth prefixes infinite
    exact Or.inr ⟨N,start,absent,final_phase_parity_iff P closed d controllers σ impl
      step q₀ history depth prefixes live priority N start absent⟩

end Parity
end Characterisation
