/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.PhaseStrategyComposition

/-! Monitor composition uses the state of the actual preceding run.
A newly selected controller is evaluated on full views, but its hypothetical
outputs before the phase are never used to reconstruct the incoming state. -/
namespace Characterisation
open DistributedSynthesis

def strategyContinuationLabel {I₁ I₂ O₁ O₂ Q : Type}
    (σ : StrategyPair I₁ I₂ O₁ O₂)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
    (initial : Q) (root word : EnvHistory I₁ I₂) : Q :=
  (word.foldl (strategyLabelStep σ step) (root,initial)).2

theorem strategyHistoryLabel_continuation {I₁ I₂ O₁ O₂ Q : Type}
    (σ : StrategyPair I₁ I₂ O₁ O₂)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
    (q₀ : Q) (root word : EnvHistory I₁ I₂) :
    strategyHistoryLabel σ step q₀ (root++word) =
      strategyContinuationLabel σ step (strategyHistoryLabel σ step q₀ root) root word := by
  have state : root.foldl (strategyLabelStep σ step) ([],q₀) =
      (root,strategyHistoryLabel σ step q₀ root) := by
    apply Prod.ext
    · simpa only [List.nil_append] using strategyLabelStep_history σ step [] q₀ root
    · rfl
  unfold strategyHistoryLabel strategyContinuationLabel
  rw [List.foldl_append,state]

/-- Equal outputs on the nonempty prefixes of this continuation give the
same monitor run from any common incoming state. No equality is required
between the controllers' hypothetical pre-phase outputs. -/
theorem strategyLabelStep_fold_congr {I₁ I₂ O₁ O₂ Q : Type}
    (σ τ : StrategyPair I₁ I₂ O₁ O₂)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
    (root word : EnvHistory I₁ I₂) (q : Q)
    (agree : ∀ v : EnvHistory I₁ I₂, v.IsPrefix word → v ≠ [] →
      (σ.one (currentView .one (root++v)),σ.two (currentView .two (root++v))) =
      (τ.one (currentView .one (root++v)),τ.two (currentView .two (root++v)))) :
    word.foldl (strategyLabelStep σ step) (root,q) =
      word.foldl (strategyLabelStep τ step) (root,q) := by
  induction word generalizing root q with
  | nil => rfl
  | cons r word ih =>
    have first := agree [r] ⟨word,rfl⟩ (by simp)
    simp only [List.foldl_cons,strategyLabelStep]
    rw [first]
    apply ih
    intro v pref _
    obtain ⟨u,eq⟩ := pref
    have result := agree ([r]++v) ⟨u,by simpa only [List.append_assoc,List.singleton_append] using congrArg (List.cons r) eq⟩
      (by simp)
    simpa only [List.append_assoc] using result

theorem strategyContinuationLabel_congr {I₁ I₂ O₁ O₂ Q : Type}
    (σ τ : StrategyPair I₁ I₂ O₁ O₂)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
    (root word : EnvHistory I₁ I₂) (q : Q)
    (agree : ∀ v : EnvHistory I₁ I₂, v.IsPrefix word → v ≠ [] →
      (σ.one (currentView .one (root++v)),σ.two (currentView .two (root++v))) =
      (τ.one (currentView .one (root++v)),τ.two (currentView .two (root++v)))) :
    strategyContinuationLabel σ step q root word = strategyContinuationLabel τ step q root word :=
  congrArg Prod.snd (strategyLabelStep_fold_congr σ τ step root word q agree)

/-- The composed strategy and selected phase controller agree at every
nonempty prefix of the actual phase, including its closing boundary. -/
theorem phase_implementation_on_prefixes {I₁ I₂ O₁ O₂ : Type}
    (P : List Graph → Prop) (closed : PrefixClosed P) (d : Nat)
    (controllers : LeaderPhaseOrigin I₁ I₂ → StrategyPair I₁ I₂ O₁ O₂)
    (σ : StrategyPair I₁ I₂ O₁ O₂) (impl : ImplementsPhaseFamily P d controllers σ)
    (root word : EnvHistory I₁ I₂) (live : P (History.graphSequence (root++word)))
    (phase : LeaderPhaseInterval P d (root++word) (List.length root)) :
    ∀ v : EnvHistory I₁ I₂, v.IsPrefix word → v ≠ [] →
      (σ.one (currentView .one (root++v)),σ.two (currentView .two (root++v))) =
        ((controllers (List.length root,inputComponentSet P root)).one (currentView .one (root++v)),
         (controllers (List.length root,inputComponentSet P root)).two (currentView .two (root++v))) := by
  intro v pref nonempty
  obtain ⟨u,eq⟩ := pref
  have full : root++word = (root++v)++u := by rw [← eq,List.append_assoc]
  have lower : List.length root < List.length (root++v) := by
    have positive := List.length_pos_iff.mpr nonempty
    simp only [List.length_append]
    omega
  have upper : List.length (root++v) ≤ List.length (root++word) := by
    rw [full]
    simp only [List.length_append]
    omega
  have takeEq : (root++word).take (List.length (root++v)) = root++v := by
    rw [full,List.take_left]
  have correct := phase_implementation_on_interval P closed d controllers σ impl
    (root++word) live (List.length root) phase (List.length (root++v)) lower upper
  simpa only [takeEq,List.take_left] using correct

/-- A whole phase transports the actual incoming monitor state to the
actual outgoing state. This holds for both leader orientations and arbitrary
finite private-input words, without resetting the specification monitor. -/
theorem phase_monitor_replay {I₁ I₂ O₁ O₂ Q : Type}
    (P : List Graph → Prop) (closed : PrefixClosed P) (d : Nat)
    (controllers : LeaderPhaseOrigin I₁ I₂ → StrategyPair I₁ I₂ O₁ O₂)
    (σ : StrategyPair I₁ I₂ O₁ O₂) (impl : ImplementsPhaseFamily P d controllers σ)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (q₀ : Q)
    (root word : EnvHistory I₁ I₂) (live : P (History.graphSequence (root++word)))
    (phase : LeaderPhaseInterval P d (root++word) (List.length root)) :
    strategyHistoryLabel σ step q₀ (root++word) =
      strategyContinuationLabel (controllers (List.length root,inputComponentSet P root)) step
        (strategyHistoryLabel σ step q₀ root) root word := by
  rw [strategyHistoryLabel_continuation]
  exact strategyContinuationLabel_congr σ _ step root word _
    (phase_implementation_on_prefixes P closed d controllers σ impl root word live phase)

/-- Boundary states computed by successive phase controllers. Each update
starts at the previous carried state and reads every round of its phase. -/
def phaseBoundaryLabels {I₁ I₂ O₁ O₂ Q : Type}
    (P : List Graph → Prop)
    (controllers : LeaderPhaseOrigin I₁ I₂ → StrategyPair I₁ I₂ O₁ O₂)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (q₀ : Q)
    (roots words : Nat → EnvHistory I₁ I₂) : Nat → Q
  | 0 => q₀
  | n+1 => strategyContinuationLabel
      (controllers (List.length (roots n),inputComponentSet P (roots n))) step
      (phaseBoundaryLabels P controllers step q₀ roots words n) (roots n) (words n)

/-- Carried states remain equal to the one composed strategy's full-history
run after arbitrarily many phase changes. No bound on phase lengths or on
the number of changes is used. Global parity winning is a separate property. -/
theorem phase_boundary_labels_exact {I₁ I₂ O₁ O₂ Q : Type}
    (P : List Graph → Prop) (closed : PrefixClosed P) (d : Nat)
    (controllers : LeaderPhaseOrigin I₁ I₂ → StrategyPair I₁ I₂ O₁ O₂)
    (σ : StrategyPair I₁ I₂ O₁ O₂) (impl : ImplementsPhaseFamily P d controllers σ)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (q₀ : Q)
    (roots words : Nat → EnvHistory I₁ I₂) (initial : roots 0 = [])
    (next : ∀ n, roots (n+1) = roots n ++ words n)
    (live : ∀ n, P (History.graphSequence (roots (n+1))))
    (phases : ∀ n, LeaderPhaseInterval P d (roots (n+1)) (List.length (roots n))) :
    ∀ n, phaseBoundaryLabels P controllers step q₀ roots words n =
      strategyHistoryLabel σ step q₀ (roots n) := by
  intro n
  induction n with
  | zero => simp only [phaseBoundaryLabels,initial,strategyHistoryLabel,List.foldl_nil]
  | succ n ih =>
    rw [phaseBoundaryLabels,ih,next n]
    exact (phase_monitor_replay P closed d controllers σ impl step q₀ (roots n) (words n)
      (by rw [← next n]; exact live n) (by rw [← next n]; exact phases n)).symm

end Characterisation
