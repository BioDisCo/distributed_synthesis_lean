/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.InputKnowledge

/-! Common input information survives component refinement. At a change of
selected process, older prefixes of both input streams are common. -/
namespace Characterisation
open DistributedSynthesis

private theorem previous_current {I₁ I₂ O₁ O₂ : Type*}
    (p : Proc) (h : History I₁ I₂ Graph O₁ O₂) :
    (currentView p h).nonFringe.previousView = currentView p h.dropLast := by
  cases h using List.reverseRecOn with
  | nil => cases p <;> rfl
  | append_singleton h r =>
    simp only [List.dropLast_concat]
    cases p
    · change (currentView .one (History.append h r)).nonFringe.previousView = _
      rw [currentView_one_append]
      cases r.graph <;> rfl
    · change (currentView .two (History.append h r)).nonFringe.previousView = _
      rw [currentView_two_append]
      cases r.graph <;> rfl

theorem inputAdjacent_parent {I₁ I₂ O₁ O₂ : Type*}
    {h k : History I₁ I₂ Graph O₁ O₂} (adj : InputAdjacent h k) :
    InputAdjacent h.dropLast k.dropLast := by
  rcases adj with eq | eq
  · left
    have hp := congrArg (fun v => v.nonFringe.previousView) eq
    simpa only [previous_current] using hp
  · right
    have hp := congrArg (fun v => v.nonFringe.previousView) eq
    simpa only [previous_current] using hp

theorem graphSequence_dropLast {I₁ I₂ O₁ O₂ : Type*}
    (h : History I₁ I₂ Graph O₁ O₂) :
    History.graphSequence h.dropLast = (History.graphSequence h).dropLast := by
  simp [History.graphSequence]

theorem inputConnected_parent {I₁ I₂ O₁ O₂ : Type*}
    (P : List Graph → Prop) (closed : PrefixClosed P)
    {h k : History I₁ I₂ Graph O₁ O₂} (conn : InputConnected P h k) :
    InputConnected P h.dropLast k.dropLast := by
  apply Relation.ReflTransGen.lift List.dropLast _ conn
  intro a b step
  refine ⟨?_, ?_, inputAdjacent_parent step.2.2⟩
  · rw [graphSequence_dropLast]
    exact live_parent P closed step.1
  · rw [graphSequence_dropLast]
    exact live_parent P closed step.2.1

/-- The new component preserves both the previous selected input prefix and
its own selected input prefix. When owners differ these are prefixes of both
input streams, with respective delays d+1 and d. -/
theorem common_prefixes_at_handoff {I₁ I₂ O₁ O₂ : Type*}
    (P : List Graph → Prop) (closed : PrefixClosed P) (d : Nat)
    (previousOwner currentOwner : Proc) {h k : History I₁ I₂ Graph O₁ O₂}
    (previousRecent : RecentOther P d (History.graphSequence h.dropLast) previousOwner)
    (currentRecent : RecentOther P d (History.graphSequence h) currentOwner)
    (conn : InputConnected P h k) :
    olderInputPrefix previousOwner d h.dropLast = olderInputPrefix previousOwner d k.dropLast ∧
    olderInputPrefix currentOwner d h = olderInputPrefix currentOwner d k :=
  ⟨selected_prefix_component P d previousOwner previousRecent (inputConnected_parent P closed conn),
   selected_prefix_component P d currentOwner currentRecent conn⟩

/-- A common graph-based choice of owners with the prefix invariants required
both within a component and at every one-round handoff. -/
theorem holes_common_prefixes_at_handoff {I₁ I₂ O₁ O₂ : Type*}
    (A : Set (Nat → Graph)) (regular : OmegaRegular A) (holes : GeometricHoles A) :
    ∃ d, ∀ h : History I₁ I₂ Graph O₁ O₂, LivePrefix A (History.graphSequence h) →
      ∀ k, InputConnected (LivePrefix A) h k →
        olderInputPrefix (componentLeader (LivePrefix A) d (History.graphSequence h.dropLast))
            d h.dropLast =
          olderInputPrefix (componentLeader (LivePrefix A) d (History.graphSequence h.dropLast))
            d k.dropLast ∧
        olderInputPrefix (componentLeader (LivePrefix A) d (History.graphSequence h)) d h =
          olderInputPrefix (componentLeader (LivePrefix A) d (History.graphSequence h)) d k := by
  obtain ⟨d, recent⟩ := holes_component_recent_receiver A regular holes
  refine ⟨d, ?_⟩
  intro h hh k conn
  have parentLive : LivePrefix A (History.graphSequence h.dropLast) := by
    rw [graphSequence_dropLast]
    exact live_parent _ (livePrefix_closed A) hh
  exact common_prefixes_at_handoff _ (livePrefix_closed A) d _ _
    (componentLeader_correct _ d _ (recent _ parentLive))
    (componentLeader_correct _ d _ (recent _ hh)) conn

theorem olderInputPrefix_parent {I₁ I₂ O₁ O₂ : Type*} (p : Proc) (d : Nat)
    (h : History I₁ I₂ Graph O₁ O₂) :
    olderInputPrefix p d h.dropLast = olderInputPrefix p (d+1) h := by
  cases h using List.reverseRecOn with
  | nil => simp [olderInputPrefix, inputWord, History.length]
  | append_singleton h r =>
    simp [olderInputPrefix, inputWord, History.length, List.take_append]

private theorem more_delay {I₁ I₂ O₁ O₂ : Type*} (p : Proc) (d : Nat)
    {h k : History I₁ I₂ Graph O₁ O₂} (len : h.length = k.length)
    (eq : olderInputPrefix p d h = olderInputPrefix p d k) :
    olderInputPrefix p (d+1) h = olderInputPrefix p (d+1) k := by
  have cut := congrArg (List.take (h.length-(d+1))) eq
  unfold olderInputPrefix at cut ⊢
  rw [← len] at cut ⊢
  simpa only [List.take_take, min_eq_left (by omega : h.length-(d+1) ≤ h.length-d)] using cut

/-- On a change of owner, both input prefixes through depth t-(d+1) are
constant over the child component. Thus only the last d+1 input rounds can
vary there; the graph histories are bounded separately by graph holes. -/
theorem both_input_prefixes_at_switch {I₁ I₂ O₁ O₂ : Type*}
    (P : List Graph → Prop) (closed : PrefixClosed P) (d : Nat)
    (previousOwner currentOwner : Proc) {h k : History I₁ I₂ Graph O₁ O₂}
    (changed : previousOwner ≠ currentOwner)
    (previousRecent : RecentOther P d (History.graphSequence h.dropLast) previousOwner)
    (currentRecent : RecentOther P d (History.graphSequence h) currentOwner)
    (conn : InputConnected P h k) :
    olderInputPrefix .one (d+1) h = olderInputPrefix .one (d+1) k ∧
    olderInputPrefix .two (d+1) h = olderInputPrefix .two (d+1) k := by
  have both := common_prefixes_at_handoff P closed d previousOwner currentOwner
    previousRecent currentRecent conn
  have len : h.length = k.length := by
    have eq := connected_same_depth P (inputConnected_projects P conn)
    simpa [History.graphSequence] using eq
  rw [olderInputPrefix_parent, olderInputPrefix_parent] at both
  have current := more_delay currentOwner d len both.2
  cases previousOwner <;> cases currentOwner
  · exact False.elim (changed rfl)
  · exact ⟨both.1, current⟩
  · exact ⟨current, both.1⟩
  · exact False.elim (changed rfl)

end Characterisation
