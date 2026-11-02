/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.CoordinatorResponses

/-! The commonly selected process has outgoing deliveries. Selection must
not choose a permanent receiver that cannot send instructions back. -/
namespace Characterisation
open DistributedSynthesis FullViewPath

def receivesGraph : Proc → Graph → Bool
  | .one, .right => false
  | .two, .left => false
  | _, _ => true

def DeliversFrom (p : Proc) (g : Graph) : Prop := receivesGraph p.other g = true

private theorem silentAge_append (p : Proc) (h : List Graph) (g : Graph) :
    silentAge (graphView p (h ++ [g])) =
      if receivesGraph p g then 0 else silentAge (graphView p h) + 1 := by
  cases p <;> cases g <;> simp [graphView, at_append, advance, advanceViews, silentAge, receivesGraph]

/-- A recent reception is witnessed by an actual delivered graph, with fewer
than d subsequent rounds. -/
theorem recent_receive_factor (p : Proc) (h : List Graph) (d : Nat)
    (deep : d ≤ h.length) (recent : silentAge (graphView p h) < d) :
    ∃ a g b, h = a ++ [g] ++ b ∧ b.length < d ∧ receivesGraph p g = true := by
  induction h using List.reverseRecOn generalizing d with
  | nil => simp at deep; omega
  | append_singleton h g ih =>
    rw [silentAge_append] at recent
    by_cases recv : receivesGraph p g = true
    · exact ⟨h,g,[],by simp,by simp; omega,recv⟩
    · simp only [recv, Bool.false_eq_true, ↓reduceIte] at recent
      have priorAge : silentAge (graphView p h) < d-1 := by
        omega
      obtain ⟨a,r,b,eq,len,hr⟩ := ih (d-1) (by simp at deep; omega) priorAge
      refine ⟨a,r,b++[g],?_,?_,hr⟩
      · simp [eq, List.append_assoc]
      · simp only [List.length_append, List.length_singleton]
        omega

/-- The selected process, not just its counterpart, can send: within every
past window of d rounds there is a graph delivering its message. -/
theorem recentOther_outgoing_delivery (P : List Graph → Prop) (d : Nat)
    (h : List Graph) (p : Proc) (deep : d ≤ h.length) (recent : RecentOther P d h p) :
    ∃ a g b, h = a ++ [g] ++ b ∧ b.length < d ∧ DeliversFrom p g := by
  have noBlind : ¬ BlindFor d (tagView (graphView p.other h)) := by
    apply recent h _ Relation.ReflTransGen.refl
    · cases p <;> [exact Or.inr rfl; exact Or.inl rfl]
    · cases p <;> simp [Proc.other, tagView, graphView, viewOwner]
  have age : silentAge (graphView p.other h) < d := by
    by_contra bad
    exact noBlind (silentAge_implies_blindFor d p.other h (by omega))
  exact recent_receive_factor p.other h d deep age

/-- Outgoing-delivery guarantee for the canonical, locally agreed coordinator. -/
theorem holes_coordinator_outgoing_delivery (A : Set (Nat → Graph))
    (regular : OmegaRegular A) (holes : GeometricHoles A) :
    ∃ d, ∀ h, LivePrefix A h → d ≤ h.length →
      ∃ a g b, h = a ++ [g] ++ b ∧ b.length < d ∧
        DeliversFrom (componentLeader (LivePrefix A) d h) g := by
  obtain ⟨d,recent⟩ := holes_component_recent_receiver A regular holes
  refine ⟨d,?_⟩
  intro h hh deep
  exact recentOther_outgoing_delivery _ d h _ deep
    (componentLeader_correct _ d h (recent h hh))

private theorem silentAge_without_deliveries (p : Proc) (h u : List Graph)
    (none : ∀ g ∈ u, receivesGraph p g = false) :
    silentAge (graphView p (h ++ u)) = silentAge (graphView p h) + u.length := by
  induction u using List.reverseRecOn with
  | nil => simp
  | append_singleton u g ih =>
    rw [← List.append_assoc, silentAge_append]
    have ng : receivesGraph p g = false := none g (by simp)
    have nu : ∀ r ∈ u, receivesGraph p r = false := fun r hr => none r (by simp [hr])
    simp [ng, ih nu, Nat.add_assoc]

/-- If the same process is selected at the end of a window of d new rounds,
it has delivered a message during those new rounds. -/
theorem recentOther_delivery_in_extension (P : List Graph → Prop) (d : Nat)
    (p : Proc) (h u : List Graph) (window : u.length = d)
    (recent : RecentOther P d (h ++ u) p) : ∃ g ∈ u, DeliversFrom p g := by
  classical
  by_contra bad
  have none : ∀ g ∈ u, receivesGraph p.other g = false := by
    intro g hg
    have no : ¬ receivesGraph p.other g = true := fun yes => bad ⟨g,hg,yes⟩
    exact Bool.eq_false_iff.mpr no
  have age := silentAge_without_deliveries p.other h u none
  have blind : BlindFor d (tagView (graphView p.other (h ++ u))) :=
    silentAge_implies_blindFor d p.other (h ++ u) (by rw [age,window]; omega)
  apply recent (h ++ u) _ Relation.ReflTransGen.refl _ _ blind
  · cases p <;> [exact Or.inr rfl; exact Or.inl rfl]
  · cases p <;> simp [Proc.other, tagView, graphView, viewOwner]

theorem holes_coordinator_delivery_within_window (A : Set (Nat → Graph))
    (regular : OmegaRegular A) (holes : GeometricHoles A) :
    ∃ d, ∀ h u, LivePrefix A (h ++ u) → u.length = d →
      componentLeader (LivePrefix A) d (h ++ u) = componentLeader (LivePrefix A) d h →
      ∃ g ∈ u, DeliversFrom (componentLeader (LivePrefix A) d h) g := by
  obtain ⟨d,recent⟩ := holes_component_recent_receiver A regular holes
  refine ⟨d,?_⟩
  intro h u live window same
  have hr := componentLeader_correct _ d (h ++ u) (recent _ live)
  rw [same] at hr
  exact recentOther_delivery_in_extension _ d _ h u window hr

end Characterisation
