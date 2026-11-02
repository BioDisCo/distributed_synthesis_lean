/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.FiniteLeaderGroups

/-! The controller for an output is selected at the most recent strictly
previous agreed boundary. A boundary round still belongs to the ending
phase. The origin is a semantic component identifier, not a finite code. -/
namespace Characterisation
open DistributedSynthesis

noncomputable def previousLeaderBoundary {I₁ I₂ : Type}
    (P : List Graph → Prop) (d : Nat) (h : EnvHistory I₁ I₂) : Nat := by
  classical
  exact Nat.findGreatest (fun a => a = 0 ∨ leaderBoundary P d (h.take a) = true)
    (List.length h - 1)

/-- A phase starts at depth zero or an agreed boundary, and has no further
boundary strictly before its current output. Its last round may be a boundary. -/
structure LeaderPhaseInterval {I₁ I₂ : Type}
    (P : List Graph → Prop) (d : Nat) (h : EnvHistory I₁ I₂) (a : Nat) : Prop where
  start_lt : a < List.length h
  start : a = 0 ∨ leaderBoundary P d (h.take a) = true
  no_boundary : ∀ n, a < n → n < List.length h → leaderBoundary P d (h.take n) = false

/-- Every nonempty history belongs to the phase selected by the strict
previous-boundary convention, including the initial phase. -/
theorem previousLeaderBoundary_interval {I₁ I₂ : Type}
    (P : List Graph → Prop) (d : Nat) (h : EnvHistory I₁ I₂) (positive : 0 < List.length h) :
    LeaderPhaseInterval P d h (previousLeaderBoundary P d h) := by
  classical
  have bound : previousLeaderBoundary P d h ≤ List.length h - 1 := Nat.findGreatest_le _
  refine ⟨by omega,?_,?_⟩
  · exact Nat.findGreatest_spec (P := fun n => n = 0 ∨ leaderBoundary P d (h.take n) = true)
      (Nat.zero_le _) (Or.inl rfl)
  · intro n lower upper
    apply Bool.eq_false_iff.mpr
    intro yes
    have lowerBound : n ≤ previousLeaderBoundary P d h :=
      Nat.le_findGreatest (by omega) (Or.inr yes)
    omega

theorem previousLeaderBoundary_eq {I₁ I₂ : Type}
    (P : List Graph → Prop) (d : Nat) (h : EnvHistory I₁ I₂) (a : Nat)
    (phase : LeaderPhaseInterval P d h a) : previousLeaderBoundary P d h = a := by
  classical
  have lower : a ≤ previousLeaderBoundary P d h :=
    Nat.le_findGreatest (by have := phase.start_lt; omega) phase.start
  have bound : previousLeaderBoundary P d h ≤ List.length h - 1 := Nat.findGreatest_le _
  have marked : previousLeaderBoundary P d h = 0 ∨
      leaderBoundary P d (h.take (previousLeaderBoundary P d h)) = true :=
    Nat.findGreatest_spec (P := fun n => n = 0 ∨ leaderBoundary P d (h.take n) = true)
      (Nat.zero_le _) (Or.inl rfl)
  by_contra ne
  have greater : a < previousLeaderBoundary P d h := by omega
  rcases marked with zero | yes
  · omega
  · have no := phase.no_boundary _ greater (by have := phase.start_lt; omega)
    rw [no] at yes
    contradiction

theorem leaderPhaseInterval_take {I₁ I₂ : Type}
    (P : List Graph → Prop) (d : Nat) (h : EnvHistory I₁ I₂) (a : Nat)
    (phase : LeaderPhaseInterval P d h a) (n : Nat) (lower : a < n) (upper : n ≤ List.length h) :
    LeaderPhaseInterval P d (h.take n) a := by
  have len : List.length (h.take n) = n := by simp only [List.length_take,min_eq_left upper]
  refine ⟨by rw [len]; exact lower,?_,?_⟩
  · simpa only [List.take_take,min_eq_left (Nat.le_of_lt lower)] using phase.start
  · intro t lo hi
    rw [len] at hi
    rw [List.take_take,min_eq_left (Nat.le_of_lt hi)]
    exact phase.no_boundary t lo (lt_of_lt_of_le hi upper)

theorem inputConnected_symm {I₁ I₂ : Type}
    (P : List Graph → Prop) {h k : EnvHistory I₁ I₂}
    (conn : InputConnected P h k) : InputConnected P k h := by
  apply Relation.ReflTransGen.symmetric (r := fun h k : EnvHistory I₁ I₂ =>
    P (History.graphSequence h) ∧ P (History.graphSequence k) ∧ InputAdjacent h k) ?_ conn
  intro h k edge
  exact ⟨edge.2.1,edge.1,edge.2.2.imp Eq.symm Eq.symm⟩

def inputComponentSet {I₁ I₂ : Type} (P : List Graph → Prop) (h : EnvHistory I₁ I₂) :
    Set (EnvHistory I₁ I₂) := {k | InputConnected P h k}

theorem inputComponentSet_eq {I₁ I₂ : Type} (P : List Graph → Prop)
    {h k : EnvHistory I₁ I₂} (conn : InputConnected P h k) :
    inputComponentSet P h = inputComponentSet P k := by
  ext r
  exact ⟨fun hr => (inputConnected_symm P conn).trans hr,fun kr => conn.trans kr⟩

abbrev LeaderPhaseOrigin (I₁ I₂ : Type) := Nat × Set (EnvHistory I₁ I₂)

noncomputable def leaderPhaseOrigin {I₁ I₂ : Type}
    (P : List Graph → Prop) (d : Nat) (h : EnvHistory I₁ I₂) : LeaderPhaseOrigin I₁ I₂ :=
  let a := previousLeaderBoundary P d h
  (a,inputComponentSet P (h.take a))

theorem leaderPhaseOrigin_component {I₁ I₂ : Type}
    (P : List Graph → Prop) (closed : PrefixClosed P) (d : Nat)
    (recent : ∀ g, P g → ∃ p, RecentOther P d g p)
    {h k : EnvHistory I₁ I₂} (live : P (History.graphSequence h))
    (conn : InputConnected P h k) : leaderPhaseOrigin P d h = leaderPhaseOrigin P d k := by
  classical
  have flags := leaderBoundary_history_component P closed d recent live conn
  have lengths := inputConnected_length P conn
  have previous : previousLeaderBoundary P d h = previousLeaderBoundary P d k := by
    unfold previousLeaderBoundary
    simp only [flags,lengths]
  simp only [leaderPhaseOrigin,previous]
  exact congrArg (Prod.mk _) (inputComponentSet_eq P (inputConnected_take P closed conn _))

/-- Both processes retain the same phase origin at every output through
and including the next boundary. Equalities concern actual absolute depths. -/
theorem leaderPhaseOrigin_on_interval {I₁ I₂ : Type}
    (P : List Graph → Prop) (d : Nat) (h : EnvHistory I₁ I₂) (a : Nat)
    (phase : LeaderPhaseInterval P d h a) (n : Nat) (lower : a < n) (upper : n ≤ List.length h) :
    leaderPhaseOrigin P d (h.take n) = (a,inputComponentSet P (h.take a)) := by
  simp only [leaderPhaseOrigin,previousLeaderBoundary_eq P d (h.take n) a
    (leaderPhaseInterval_take P d h a phase n lower upper),List.take_take,
    min_eq_left (Nat.le_of_lt lower)]

end Characterisation
