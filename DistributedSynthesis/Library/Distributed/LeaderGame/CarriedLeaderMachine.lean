/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.PublicHandoverRecursion
import DistributedSynthesis.Library.Distributed.LeaderGame.LeaderAnnotationSemantics

/-! A common boundary machine carries labels indexed by literal histories.
Every label and phase minimum is computed by replaying the selected leader's
controller from the preceding boundary state. This construction proves the
global annotation invariant for the one composed distributed strategy. -/
namespace Characterisation
open DistributedSynthesis

structure CarriedLeaderState (Data Q I₁ I₂ : Type) where
  data : Data
  label : EnvHistory I₁ I₂ → Q
  minimum : EnvHistory I₁ I₂ → Nat

section
variable {Data Q I₁ I₂ O₁ O₂ : Type}
variable (P : List Graph → Prop) (d : Nat)
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
variable (priority : Q → Nat) (q₀ : Q) (initialData : Data)
variable (decode : LeaderPhaseOrigin I₁ I₂ → CarriedLeaderState Data Q I₁ I₂ → StrategyPair I₁ I₂ O₁ O₂)
variable (update : CarriedLeaderState Data Q I₁ I₂ → LeaderPhaseOrigin I₁ I₂ →
  LeaderPhaseOrigin I₁ I₂ → (EnvHistory I₁ I₂ → Q) → (EnvHistory I₁ I₂ → Nat) → Data)

def initialCarriedLeaderState : CarriedLeaderState Data Q I₁ I₂ :=
  ⟨initialData,fun _ => q₀,fun _ => priority q₀⟩

def carriedLeaderAdvance (state : CarriedLeaderState Data Q I₁ I₂)
    (old target : LeaderPhaseOrigin I₁ I₂) : CarriedLeaderState Data Q I₁ I₂ :=
  let controller := decode old state
  let label := fun h : EnvHistory I₁ I₂ => strategyContinuationLabel controller step
    (state.label (h.take old.1)) (h.take old.1) (h.drop old.1)
  let minimum := fun h : EnvHistory I₁ I₂ => rangeMin
    (fun i => priority (strategyContinuationLabel controller step
      (state.label (h.take old.1)) (h.take old.1) ((h.drop old.1).take (i+1))))
    0 (List.length h-old.1-1)
  ⟨update state old target label minimum,label,minimum⟩

noncomputable abbrev carriedLeaderMachine := boundaryMachine P d
  (initialCarriedLeaderState priority q₀ initialData) (carriedLeaderAdvance step priority decode update)

variable (closed : PrefixClosed P)
variable (recent : ∀ g, P g → ∃ p, RecentOther P d g p)

include closed recent in
/-- A single distributed strategy implements all recursively selected leader
controllers. Its carried objective labels are exact after arbitrarily many
handovers, and its stored minima cover all original physical rounds. The
public data update is unrestricted; game legality is a separate obligation. -/
theorem carriedLeaderMachine_realization :
    ∃ read : LeaderPhaseOrigin I₁ I₂ → CarriedLeaderState Data Q I₁ I₂,
    ∃ σ : StrategyPair I₁ I₂ O₁ O₂,
      (∀ h : EnvHistory I₁ I₂, P (History.graphSequence h) →
        read (boundaryOrigin P h) = carriedLeaderMachine P d step priority q₀ initialData decode update h) ∧
      ImplementsPhaseFamily P d (fun origin => decode origin (read origin)) σ ∧
      (∀ h : EnvHistory I₁ I₂, P (History.graphSequence h) →
        (carriedLeaderMachine P d step priority q₀ initialData decode update h).label h =
          strategyHistoryLabel σ step q₀ h) ∧
      ∀ h : EnvHistory I₁ I₂, P (History.graphSequence h) → 0 < List.length h →
        (carriedLeaderMachine P d step priority q₀ initialData decode update h).minimum h =
          historyPhaseMinimum (fun k => priority (strategyHistoryLabel σ step q₀ k))
            (previousLeaderBoundary P d h) (List.length h) h := by
  obtain ⟨read,σ,reads,impl,_⟩ := boundaryMachine_strategy P d
    (initialCarriedLeaderState priority q₀ initialData) (carriedLeaderAdvance step priority decode update)
    closed recent decode
  let machine := carriedLeaderMachine P d step priority q₀ initialData decode update
  let controllers := fun origin => decode origin (read origin)
  have labels : ∀ n (h : EnvHistory I₁ I₂), List.length h = n → P (History.graphSequence h) →
      (machine h).label h = strategyHistoryLabel σ step q₀ h := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro h length live
      by_cases empty : h = []
      · subst h
        change (boundaryMachine P d (initialCarriedLeaderState priority q₀ initialData)
          (carriedLeaderAdvance step priority decode update) []).label [] = _
        rw [boundaryMachine_empty]
        rfl
      · have positive : 0 < List.length h := List.length_pos_iff.mpr empty
        let a := previousLeaderBoundary P d h
        have phase := previousLeaderBoundary_interval P d h positive
        have less : a < List.length h := phase.start_lt
        have rootLength : List.length (h.take a) = a := by
          simp only [List.length_take,min_eq_left (Nat.le_of_lt less)]
        have liveRoot := live_history_take P closed h live a
        have incoming := ih a (by omega) (h.take a) rootLength liveRoot
        have sameOrigin : (List.length (h.take a),inputComponentSet P (h.take a)) =
            boundaryOrigin P (h.take a) := rfl
        have replay := phase_monitor_replay P closed d controllers σ impl step q₀ (h.take a) (h.drop a)
          (by simpa only [List.take_append_drop] using live)
          (by simpa only [List.take_append_drop,rootLength] using phase)
        rw [List.take_append_drop,sameOrigin] at replay
        dsimp only [controllers] at replay
        rw [reads _ liveRoot] at replay
        change (boundaryMachine P d (initialCarriedLeaderState priority q₀ initialData)
          (carriedLeaderAdvance step priority decode update) h).label h = _
        rw [boundaryMachine_nonempty P d _ _ h empty]
        change strategyContinuationLabel (decode (boundaryOrigin P (h.take a)) (machine (h.take a))) step
          ((machine (h.take a)).label (h.take (List.length (h.take a))))
          (h.take (List.length (h.take a))) (h.drop (List.length (h.take a))) = _
        rw [rootLength,incoming]
        exact replay.symm
  refine ⟨read,σ,reads,impl,(fun h live => labels _ h rfl live),?_⟩
  intro h live positive
  let a := previousLeaderBoundary P d h
  have phase := previousLeaderBoundary_interval P d h positive
  have less : a < List.length h := phase.start_lt
  have rootLength : List.length (h.take a) = a := by
    simp only [List.length_take,min_eq_left (Nat.le_of_lt less)]
  have liveRoot := live_history_take P closed h live a
  have incoming := labels _ (h.take a) rfl liveRoot
  have empty : h ≠ [] := List.ne_nil_of_length_pos positive
  change (boundaryMachine P d (initialCarriedLeaderState priority q₀ initialData)
    (carriedLeaderAdvance step priority decode update) h).minimum h = _
  rw [boundaryMachine_nonempty P d _ _ h empty]
  change rangeMin (fun i => priority (strategyContinuationLabel
    (decode (boundaryOrigin P (h.take a)) (machine (h.take a))) step
    ((machine (h.take a)).label (h.take (List.length (h.take a))))
    (h.take (List.length (h.take a))) ((h.drop (List.length (h.take a))).take (i+1))))
    0 (List.length h-List.length (h.take a)-1) = _
  rw [rootLength,incoming]
  unfold historyPhaseMinimum
  apply rangeMin_congr
  intro i bound
  have within : a+(i+1) ≤ List.length h := by omega
  have pref : h.take a ++ (h.drop a).take (i+1) = h.take (a+(i+1)) :=
    List.take_add.symm
  have shorter := leaderPhaseInterval_take P d h a phase (a+(i+1)) (by omega) within
  have shorter' : LeaderPhaseInterval P d (h.take a ++ (h.drop a).take (i+1))
      (List.length (h.take a)) := by simpa only [pref,rootLength] using shorter
  have replay := phase_monitor_replay P closed d controllers σ impl step q₀
    (h.take a) ((h.drop a).take (i+1))
    (by rw [pref]; exact live_history_take P closed h live _) shorter'
  rw [pref] at replay
  dsimp only [controllers] at replay
  have sameOrigin : (List.length (h.take a),inputComponentSet P (h.take a)) =
      boundaryOrigin P (h.take a) := rfl
  rw [sameOrigin] at replay
  rw [reads _ liveRoot] at replay
  simpa only [Nat.zero_add,Nat.add_assoc] using (congrArg priority replay).symm

end
end Characterisation
