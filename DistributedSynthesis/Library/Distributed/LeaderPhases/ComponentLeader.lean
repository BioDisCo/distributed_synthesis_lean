/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.GraphAdversaries.BlindWindow
import DistributedSynthesis.Library.Distributed.GraphAdversaries.ComponentStrategies

/-! A common component-dependent process can be selected from local views.
The selection is an existence theorem, not yet a finite-state construction. -/
namespace Characterisation
open DistributedSynthesis FullViewPath

def RecentOther (P : List Graph → Prop) (d : Nat) (h : List Graph) (p : Proc) : Prop :=
  ∀ k v, Connected P h k → Incident k v → viewOwner v ≠ p → ¬ BlindFor d v

theorem recentOther_component_invariant (P : List Graph → Prop) (d : Nat)
    {h k : List Graph} (conn : Connected P h k) (p : Proc) :
    RecentOther P d h p ↔ RecentOther P d k p := by
  constructor
  · intro hh j v kj hv different
    exact hh j v (conn.trans kj) hv different
  · intro hk j v hj hv different
    exact hk j v ((connected_symm P conn).trans hj) hv different

noncomputable def componentLeader (P : List Graph → Prop) (d : Nat) (h : List Graph) : Proc := by
  classical
  exact if RecentOther P d h .one then .one else .two

theorem componentLeader_correct (P : List Graph → Prop) (d : Nat) (h : List Graph)
    (existsLeader : ∃ p, RecentOther P d h p) :
    RecentOther P d h (componentLeader P d h) := by
  classical
  unfold componentLeader
  split
  · assumption
  · obtain ⟨p,hp⟩ := existsLeader
    cases p
    · contradiction
    · exact hp

theorem componentLeader_component_invariant (P : List Graph → Prop) (d : Nat)
    {h k : List Graph} (conn : Connected P h k) :
    componentLeader P d h = componentLeader P d k := by
  have eq := propext (recentOther_component_invariant P d conn .one)
  unfold componentLeader
  erw [eq]

/-- Both processes can agree on this selection using only their own graph
views. In particular, no global graph observation is added to the model. -/
theorem componentLeader_local (P : List Graph → Prop) (d : Nat) :
    ∃ σ : StrategyPair Unit Unit Proc Proc, ∀ h, P h →
      σ.one (evaluate h).one = componentLeader P d h ∧
      σ.two (evaluate h).two = componentLeader P d h := by
  letI : Nonempty Proc := ⟨.one⟩
  apply (locallyConsistent_iff_strategy P
    (fun h => (componentLeader P d h, componentLeader P d h))).mp
  constructor
  · intro h k hh hk eq
    exact componentLeader_component_invariant P d
      (Relation.ReflTransGen.single ⟨hh,hk,Or.inl eq⟩)
  · intro h k hh hk eq
    exact componentLeader_component_invariant P d
      (Relation.ReflTransGen.single ⟨hh,hk,Or.inr eq⟩)

/-- Graph holes permit a common process selection by input-aware local
strategies. Every graph view of the other process in that component has a
reception within the window, provided the history depth is at least d. -/
theorem holes_local_recent_receiver_selection {I₁ I₂ O₁ O₂ : Type*}
    (A : Set (Nat → Graph)) (regular : OmegaRegular A) (holes : GeometricHoles A) :
    ∃ d, ∃ σ : StrategyPair I₁ I₂ Proc Proc,
      ∀ h : History I₁ I₂ Graph O₁ O₂, LivePrefix A (History.graphSequence h) →
        ∃ p, σ.one (currentView .one h) = p ∧ σ.two (currentView .two h) = p ∧
          RecentOther (LivePrefix A) d (History.graphSequence h) p := by
  obtain ⟨d, recent⟩ := holes_component_recent_receiver A regular holes
  obtain ⟨τ, localSpec⟩ := componentLeader_local (LivePrefix A) d
  refine ⟨d, ⟨fun v => τ.one (eraseView v), fun v => τ.two (eraseView v)⟩, ?_⟩
  intro h hh
  refine ⟨componentLeader (LivePrefix A) d (History.graphSequence h), ?_, ?_, ?_⟩
  · change τ.one (eraseView (currentView .one h)) = _
    rw [(eraseView_history h).1]
    exact (localSpec _ hh).1
  · change τ.two (eraseView (currentView .two h)) = _
    rw [(eraseView_history h).2]
    exact (localSpec _ hh).2
  · exact componentLeader_correct _ _ _ (recent _ hh)

end Characterisation
