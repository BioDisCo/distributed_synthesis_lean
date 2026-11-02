/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.FinitePhaseReadback

/-! The entire sequence of agreed boundary flags is common throughout a
current input component. Thus histories at the next boundary have the same
previous boundary and the same agreed leader at that previous boundary. -/
namespace Characterisation
open DistributedSynthesis

theorem live_history_take {I₁ I₂ : Type*} (P : List Graph → Prop) (closed : PrefixClosed P)
    (h : EnvHistory I₁ I₂) (live : P (History.graphSequence h)) (n : Nat) :
    P (History.graphSequence (h.take n)) := by
  apply closed _ (History.graphSequence (h.drop n))
  simpa [History.graphSequence,← List.map_append] using live

theorem inputConnected_live {I₁ I₂ : Type*} (P : List Graph → Prop)
    {h k : EnvHistory I₁ I₂} (live : P (History.graphSequence h)) (conn : InputConnected P h k) :
    P (History.graphSequence k) := by
  induction conn with
  | refl => exact live
  | tail _ edge _ => exact edge.2.1

theorem inputConnected_length {I₁ I₂ : Type*} (P : List Graph → Prop)
    {h k : EnvHistory I₁ I₂} (conn : InputConnected P h k) : List.length h = List.length k := by
  have lengths := connected_same_depth P (inputConnected_projects P conn)
  simpa only [History.graphSequence,List.length_map] using lengths

/-- Perfect recall of a local boundary test gives common boundary flags
at every earlier absolute round throughout the current component. -/
theorem leaderBoundary_history_component {I₁ I₂ : Type*}
    (P : List Graph → Prop) (closed : PrefixClosed P) (d : Nat)
    (recent : ∀ g, P g → ∃ p, RecentOther P d g p)
    {h k : EnvHistory I₁ I₂} (live : P (History.graphSequence h))
    (conn : InputConnected P h k) (n : Nat) :
    leaderBoundary P d (h.take n) = leaderBoundary P d (k.take n) :=
  leaderBoundary_component P closed d _ _
    (componentLeader_correct P d _ (recent _ (live_history_take P closed h live n)))
    (inputConnected_take P closed conn n)

/-- The endpoint is the history's current depth; no endpoint is announced
in advance. The depth `a` is the preceding agreed boundary. -/
structure ConsecutiveLeaderBoundaries {I₁ I₂ : Type*}
    (P : List Graph → Prop) (d : Nat) (h : EnvHistory I₁ I₂) (a : Nat) : Prop where
  start_lt : a < List.length h
  start_boundary : leaderBoundary P d (h.take a) = true
  end_boundary : leaderBoundary P d h = true
  no_boundary : ∀ n, a < n → n < List.length h → leaderBoundary P d (h.take n) = false

theorem consecutiveLeaderBoundaries_component {I₁ I₂ : Type*}
    (P : List Graph → Prop) (closed : PrefixClosed P) (d : Nat)
    (recent : ∀ g, P g → ∃ p, RecentOther P d g p)
    {h k : EnvHistory I₁ I₂} (live : P (History.graphSequence h))
    (conn : InputConnected P h k) (a : Nat) (phase : ConsecutiveLeaderBoundaries P d h a) :
    ConsecutiveLeaderBoundaries P d k a := by
  have len := inputConnected_length P conn
  have flags := leaderBoundary_history_component P closed d recent live conn
  refine ⟨by rw [← len]; exact phase.start_lt,?_,?_,?_⟩
  · rw [← flags a]
    exact phase.start_boundary
  · have endpoint := flags (List.length h)
    rw [List.take_length,len,List.take_length] at endpoint
    exact endpoint.symm.trans phase.end_boundary
  · intro n lower upper
    rw [← flags n]
    exact phase.no_boundary n lower (by omega)

theorem componentLeader_history_component {I₁ I₂ : Type*}
    (P : List Graph → Prop) (closed : PrefixClosed P) (d : Nat)
    {h k : EnvHistory I₁ I₂} (conn : InputConnected P h k) (n : Nat) :
    componentLeader P d (History.graphSequence (h.take n)) =
      componentLeader P d (History.graphSequence (k.take n)) :=
  componentLeader_component_invariant P d (inputConnected_projects P (inputConnected_take P closed conn n))

end Characterisation
