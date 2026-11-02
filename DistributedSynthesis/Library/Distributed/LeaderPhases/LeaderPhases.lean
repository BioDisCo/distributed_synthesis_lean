/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.LeaderTail

/-! Agreed leader phases end at a delayed checkpoint or a leader change.
A phase has a one-way prefix and at most d+1 closing rounds. The bound includes
the receiving round itself; it is not permission to delay any output. -/
namespace Characterisation
open DistributedSynthesis

noncomputable def leaderBoundary {I₁ I₂ : Type*}
    (P : List Graph → Prop) (d : Nat) (h : EnvHistory I₁ I₂) : Bool :=
  leaderCheckpoint P d h || decide
    (componentLeader P d (History.graphSequence h.dropLast) ≠
      componentLeader P d (History.graphSequence h))

theorem no_leaderBoundary {I₁ I₂ : Type*} (P : List Graph → Prop) (d : Nat)
    (h : EnvHistory I₁ I₂) (absent : leaderBoundary P d h = false) :
    leaderCheckpoint P d h = false ∧
      componentLeader P d (History.graphSequence h.dropLast) =
        componentLeader P d (History.graphSequence h) := by
  simpa [leaderBoundary] using absent

theorem leader_constant_between_boundaries {I₁ I₂ : Type*}
    (P : List Graph → Prop) (d : Nat)
    (history : Nat → EnvHistory I₁ I₂)
    (round : Nat → RoundRecord I₁ I₂ Graph Unit Unit)
    (step : ∀ n, history (n+1) = history n ++ [round n])
    (a b : Nat)
    (noBoundary : ∀ t, a < t → t < b → leaderBoundary P d (history t) = false) :
    ∀ t, a ≤ t → t < b →
      componentLeader P d (History.graphSequence (history t)) =
        componentLeader P d (History.graphSequence (history a)) := by
  have claim : ∀ m, a+m < b →
      componentLeader P d (History.graphSequence (history (a+m))) =
        componentLeader P d (History.graphSequence (history a)) := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro endBound
      have flags := no_leaderBoundary P d (history (a+m+1))
        (noBoundary (a+m+1) (by omega) (by omega))
      have unchanged := flags.2
      rw [step,List.dropLast_concat] at unchanged
      have previous := ih (by omega)
      rw [show a+(m+1) = (a+m)+1 by omega,step]
      exact unchanged.symm.trans previous
  intro t lower upper
  have eq : a+(t-a) = t := by omega
  simpa only [eq] using claim (t-a) (by omega)

/-- Every round except possibly the last d+1 rounds is one-way from the
leader selected at the start of the phase. Neither endpoint is assumed to
be known before it occurs. -/
theorem leader_phase_oneway_prefix {I₁ I₂ : Type*}
    (P : List Graph → Prop) (d : Nat)
    (history : Nat → EnvHistory I₁ I₂)
    (round : Nat → RoundRecord I₁ I₂ Graph Unit Unit)
    (step : ∀ n, history (n+1) = history n ++ [round n])
    (a b : Nat)
    (noBoundary : ∀ t, a < t → t < b → leaderBoundary P d (history t) = false) :
    ∀ n, a ≤ n → n+1+d < b →
      (round n).graph = leaderOutgoingGraph
        (componentLeader P d (History.graphSequence (history a))) := by
  intro n lower upper
  apply no_delayed_checkpoint_outgoing P d history round step _ n
  · exact leader_constant_between_boundaries P d history round step a b noBoundary
      (n+1+d) (by omega) upper
  · exact (no_leaderBoundary P d _ (noBoundary (n+1+d) (by omega) upper)).1

/-- Quantitative split of a finite phase: c-a one-way rounds followed by
b-c closing rounds, with b-c at most d+1. -/
theorem leader_phase_bounded_closing {I₁ I₂ : Type*}
    (P : List Graph → Prop) (d : Nat)
    (history : Nat → EnvHistory I₁ I₂)
    (round : Nat → RoundRecord I₁ I₂ Graph Unit Unit)
    (step : ∀ n, history (n+1) = history n ++ [round n])
    (a b : Nat) (ordered : a ≤ b)
    (noBoundary : ∀ t, a < t → t < b → leaderBoundary P d (history t) = false) :
    ∃ c, a ≤ c ∧ c ≤ b ∧ b-c ≤ d+1 ∧
      ∀ n, a ≤ n → n < c → (round n).graph = leaderOutgoingGraph
        (componentLeader P d (History.graphSequence (history a))) := by
  refine ⟨max a (b-(d+1)),by omega,by omega,by omega,?_⟩
  intro n lower upper
  exact leader_phase_oneway_prefix P d history round step a b noBoundary n lower (by omega)

end Characterisation
