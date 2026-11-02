/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.PhaseStrategyComposition

/-! Recursively run a public controller on the actual boundary components.
The recursion is on physical depth, not on a supplied public trace. Its
state is constant on components and therefore is available to both processes.
The closing output still belongs to the previous controller. -/
namespace Characterisation
open DistributedSynthesis

def boundaryOrigin {I₁ I₂ : Type} (P : List Graph → Prop) (h : EnvHistory I₁ I₂) :
    LeaderPhaseOrigin I₁ I₂ := ((List.length h), inputComponentSet P h)

theorem boundaryOrigin_component {I₁ I₂ : Type} (P : List Graph → Prop)
    {h k : EnvHistory I₁ I₂} (conn : InputConnected P h k) :
    boundaryOrigin P h = boundaryOrigin P k :=
  Prod.ext (inputConnected_length P conn) (inputComponentSet_eq P conn)

section Recursion
variable {I₁ I₂ State : Type}
variable (P : List Graph → Prop) (d : Nat) (initial : State)
variable (advance : State → LeaderPhaseOrigin I₁ I₂ → LeaderPhaseOrigin I₁ I₂ → State)

/-- At a nonzero boundary, first reconstruct the preceding boundary state,
then apply the transition for the whole current component. On histories
that are not boundaries this definition is merely a total extension. -/
noncomputable def boundaryMachine (h : EnvHistory I₁ I₂) : State :=
  if _empty : h = [] then initial else
    let a := previousLeaderBoundary P d h
    advance (boundaryMachine (h.take a)) (boundaryOrigin P (h.take a)) (boundaryOrigin P h)
termination_by (List.length h)
decreasing_by
  have positive : 0 < (List.length h) := by
    have nonzero : List.length h ≠ 0 := fun zero => _empty (List.eq_nil_of_length_eq_zero zero)
    omega
  have smaller := (previousLeaderBoundary_interval P d h positive).start_lt
  simpa only [List.length_take, min_eq_left (Nat.le_of_lt smaller)] using smaller

@[simp] theorem boundaryMachine_empty :
    boundaryMachine P d initial advance [] = initial := by
  rw [boundaryMachine, dif_pos rfl]

theorem boundaryMachine_nonempty (h : EnvHistory I₁ I₂) (nonempty : h ≠ []) :
    boundaryMachine P d initial advance h =
      advance (boundaryMachine P d initial advance (h.take (previousLeaderBoundary P d h)))
        (boundaryOrigin P (h.take (previousLeaderBoundary P d h))) (boundaryOrigin P h) := by
  rw [boundaryMachine, dif_neg nonempty]

variable (closed : PrefixClosed P)
variable (recent : ∀ g, P g → ∃ p, RecentOther P d g p)

include closed recent in
/-- The entire recursively computed state is common to a boundary component.
The proof uses equality of all preceding boundary flags and recursively
compares the actual predecessor components. -/
theorem boundaryMachine_component {h k : EnvHistory I₁ I₂}
    (live : P (History.graphSequence h)) (conn : InputConnected P h k) :
    boundaryMachine P d initial advance h = boundaryMachine P d initial advance k := by
  have claim : ∀ n (h k : EnvHistory I₁ I₂), (List.length h) = n →
      P (History.graphSequence h) → InputConnected P h k →
      boundaryMachine P d initial advance h = boundaryMachine P d initial advance k := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro h k len live conn
      have sameLength := inputConnected_length P conn
      by_cases empty : h = []
      · have emptyK : k = [] := List.eq_nil_of_length_eq_zero (by simpa [empty] using sameLength.symm)
        rw [empty, emptyK]
      · have positive : 0 < (List.length h) := by
          have nonzero : List.length h ≠ 0 := fun zero => empty (List.eq_nil_of_length_eq_zero zero)
          omega
        have emptyK : k ≠ [] := by
          intro eq
          apply empty
          exact List.eq_nil_of_length_eq_zero (by simpa only [eq, List.length_nil] using sameLength)
        have sameOrigin := leaderPhaseOrigin_component P closed d recent live conn
        have previous : previousLeaderBoundary P d h = previousLeaderBoundary P d k :=
          congrArg Prod.fst sameOrigin
        have smaller := (previousLeaderBoundary_interval P d h positive).start_lt
        have childLength : List.length (h.take (previousLeaderBoundary P d h)) = previousLeaderBoundary P d h :=
          by simp only [List.length_take, min_eq_left (Nat.le_of_lt smaller)]
        have recursive := ih (previousLeaderBoundary P d h) (by omega)
          (h.take (previousLeaderBoundary P d h)) (k.take (previousLeaderBoundary P d h))
          childLength (live_history_take P closed h live _)
          (inputConnected_take P closed conn _)
        rw [boundaryMachine_nonempty P d initial advance h empty,
          boundaryMachine_nonempty P d initial advance k emptyK, ← previous, recursive,
          boundaryOrigin_component P (inputConnected_take P closed conn _),
          boundaryOrigin_component P conn]
  exact claim (List.length h) h k rfl live conn

include closed recent in
/-- A single state assignment to component identifiers represents the
recursive machine at every live boundary, without choosing a hidden root. -/
theorem boundaryMachine_factors :
    ∃ read : LeaderPhaseOrigin I₁ I₂ → State,
      ∀ h : EnvHistory I₁ I₂, P (History.graphSequence h) →
        read (boundaryOrigin P h) = boundaryMachine P d initial advance h := by
  letI : Nonempty State := ⟨initial⟩
  let H := {h : EnvHistory I₁ I₂ // P (History.graphSequence h)}
  obtain ⟨read, correct⟩ := factor_local_response
    (fun h : H => boundaryOrigin P h.val)
    (fun h : H => boundaryMachine P d initial advance h.val) (by
      intro h k same
      apply boundaryMachine_component P d initial advance closed recent h.property
      have components := congrArg Prod.snd same
      change inputComponentSet P h.val = inputComponentSet P k.val at components
      have self : k.val ∈ inputComponentSet P k.val := Relation.ReflTransGen.refl
      rw [← components] at self
      exact self)
  exact ⟨read, fun h live => correct ⟨h,live⟩⟩

include closed recent in
/-- Decode each recursive boundary state as a leader table's local strategy.
The resulting single distributed strategy follows those choices at every
physical output, including the closing output of every finite phase. -/
theorem boundaryMachine_strategy {O₁ O₂ : Type}
    (decode : LeaderPhaseOrigin I₁ I₂ → State → StrategyPair I₁ I₂ O₁ O₂) :
    ∃ read : LeaderPhaseOrigin I₁ I₂ → State,
    ∃ σ : StrategyPair I₁ I₂ O₁ O₂,
      (∀ h : EnvHistory I₁ I₂, P (History.graphSequence h) →
        read (boundaryOrigin P h) = boundaryMachine P d initial advance h) ∧
      ImplementsPhaseFamily P d (fun origin => decode origin (read origin)) σ ∧
      ∀ h : EnvHistory I₁ I₂, P (History.graphSequence h) → 0 < (List.length h) →
        let a := previousLeaderBoundary P d h
        let controller := decode (boundaryOrigin P (h.take a))
          (boundaryMachine P d initial advance (h.take a))
        (σ.one (currentView .one h), σ.two (currentView .two h)) =
          (controller.one (currentView .one h), controller.two (currentView .two h)) := by
  obtain ⟨read, correct⟩ := boundaryMachine_factors P d initial advance closed recent
  obtain ⟨σ, implements⟩ := compose_leader_phases P closed d recent (fun origin => decode origin (read origin))
  refine ⟨read,σ,correct,implements,?_⟩
  intro h live positive
  have aSmall := (previousLeaderBoundary_interval P d h positive).start_lt
  have origin : leaderPhaseOrigin P d h = boundaryOrigin P (h.take (previousLeaderBoundary P d h)) := by
    apply Prod.ext
    · simp only [leaderPhaseOrigin, boundaryOrigin, List.length_take, min_eq_left (Nat.le_of_lt aSmall)]
    · rfl
  have result := implements h live positive
  rw [origin] at result
  dsimp only at result
  rw [correct _ (live_history_take P closed h live _)] at result
  exact result

end Recursion
end Characterisation
