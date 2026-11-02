/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.PhaseOrigins

/-! Compose controllers chosen at agreed boundaries. The phase index is
recovered from actual local views. This is semantic strategy composition;
the component identifier is not yet a finite game state. -/
namespace Characterisation
open DistributedSynthesis

theorem leaderPhaseOrigin_local {I₁ I₂ : Type}
    (P : List Graph → Prop) (closed : PrefixClosed P) (d : Nat)
    (recent : ∀ g, P g → ∃ p, RecentOther P d g p) :
    ∃ read : StrategyPair I₁ I₂ (LeaderPhaseOrigin I₁ I₂) (LeaderPhaseOrigin I₁ I₂),
      ∀ h : EnvHistory I₁ I₂, P (History.graphSequence h) →
        read.one (currentView .one h) = leaderPhaseOrigin P d h ∧
        read.two (currentView .two h) = leaderPhaseOrigin P d h := by
  let H := {h : EnvHistory I₁ I₂ // P (History.graphSequence h)}
  have coherent : ∀ p (h k : H), currentView p h.val = currentView p k.val →
      leaderPhaseOrigin P d h.val = leaderPhaseOrigin P d k.val := by
    intro p h k same
    apply leaderPhaseOrigin_component P closed d recent h.property
    apply Relation.ReflTransGen.single
    refine ⟨h.property,k.property,?_⟩
    cases p <;> [exact Or.inl same; exact Or.inr same]
  obtain ⟨one,oneEq⟩ := factor_local_response (fun h : H => currentView .one h.val)
    (fun h : H => leaderPhaseOrigin P d h.val) (coherent .one)
  obtain ⟨two,twoEq⟩ := factor_local_response (fun h : H => currentView .two h.val)
    (fun h : H => leaderPhaseOrigin P d h.val) (coherent .two)
  exact ⟨⟨one,two⟩,fun h live => ⟨oneEq ⟨h,live⟩,twoEq ⟨h,live⟩⟩⟩

/-- Only outputs belonging to the active phase are prescribed. A hypothetical
closing-window entry after the next boundary belongs to the next controller. -/
def ImplementsPhaseFamily {I₁ I₂ O₁ O₂ : Type}
    (P : List Graph → Prop) (d : Nat)
    (controllers : LeaderPhaseOrigin I₁ I₂ → StrategyPair I₁ I₂ O₁ O₂)
    (σ : StrategyPair I₁ I₂ O₁ O₂) : Prop :=
  ∀ h : EnvHistory I₁ I₂, P (History.graphSequence h) → 0 < List.length h →
    (σ.one (currentView .one h),σ.two (currentView .two h)) =
      ((controllers (leaderPhaseOrigin P d h)).one (currentView .one h),
       (controllers (leaderPhaseOrigin P d h)).two (currentView .two h))

/-- Arbitrarily many phase switches admit one actual local strategy pair.
The assignment of controllers is fixed on boundary components; it need not
be finite-state or winning for this local composition theorem. -/
theorem compose_leader_phases {I₁ I₂ O₁ O₂ : Type}
    (P : List Graph → Prop) (closed : PrefixClosed P) (d : Nat)
    (recent : ∀ g, P g → ∃ p, RecentOther P d g p)
    (controllers : LeaderPhaseOrigin I₁ I₂ → StrategyPair I₁ I₂ O₁ O₂) :
    ∃ σ, ImplementsPhaseFamily P d controllers σ := by
  obtain ⟨read,correct⟩ := leaderPhaseOrigin_local (I₁:=I₁) (I₂:=I₂) P closed d recent
  refine ⟨⟨fun v => (controllers (read.one v)).one v,
    fun v => (controllers (read.two v)).two v⟩,?_⟩
  intro h live _
  change ((controllers (read.one (currentView .one h))).one _,
    (controllers (read.two (currentView .two h))).two _) = _
  rw [(correct h live).1,(correct h live).2]

/-- At every physical output through the endpoint of a phase, the composed
strategy agrees with its selected controller. This includes a closing
boundary output and holds for either selected leader. -/
theorem phase_implementation_on_interval {I₁ I₂ O₁ O₂ : Type}
    (P : List Graph → Prop) (closed : PrefixClosed P) (d : Nat)
    (controllers : LeaderPhaseOrigin I₁ I₂ → StrategyPair I₁ I₂ O₁ O₂)
    (σ : StrategyPair I₁ I₂ O₁ O₂) (impl : ImplementsPhaseFamily P d controllers σ)
    (h : EnvHistory I₁ I₂) (live : P (History.graphSequence h)) (a : Nat)
    (phase : LeaderPhaseInterval P d h a) (n : Nat) (lower : a < n) (upper : n ≤ List.length h) :
    (σ.one (currentView .one (h.take n)),σ.two (currentView .two (h.take n))) =
      ((controllers (a,inputComponentSet P (h.take a))).one (currentView .one (h.take n)),
       (controllers (a,inputComponentSet P (h.take a))).two (currentView .two (h.take n))) := by
  have correct := impl (h.take n) (live_history_take P closed h live n)
    (by simp only [List.length_take,min_eq_left upper]; omega)
  rwa [leaderPhaseOrigin_on_interval P d h a phase n lower upper] at correct

theorem consecutive_boundaries_interval {I₁ I₂ : Type}
    (P : List Graph → Prop) (d : Nat) (h : EnvHistory I₁ I₂) (a : Nat)
    (phase : ConsecutiveLeaderBoundaries P d h a) : LeaderPhaseInterval P d h a :=
  ⟨phase.start_lt,Or.inr phase.start_boundary,phase.no_boundary⟩

end Characterisation
