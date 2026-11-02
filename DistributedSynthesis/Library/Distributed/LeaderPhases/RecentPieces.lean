/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.SwitchComponents

/-! Cutting indistinguishability links at views with a long nonreceiving
suffix yields uniformly bounded pieces, even inside arbitrarily long phases.
The removed links belong to the selected coordinator. Their number is not
claimed to be bounded. -/
namespace Characterisation
open DistributedSynthesis

def RecentAdjacent {I₁ I₂ : Type*} (d : Nat) (h k : EnvHistory I₁ I₂) : Prop :=
  ∃ p, currentView p h = currentView p k ∧ silentAge (currentView p h) < d

def RecentConnected {I₁ I₂ : Type*} (P : List Graph → Prop) (d : Nat) :
    EnvHistory I₁ I₂ → EnvHistory I₁ I₂ → Prop :=
  Relation.ReflTransGen (fun h k => P (History.graphSequence h) ∧
    P (History.graphSequence k) ∧ RecentAdjacent d h k)

def RecentPiece {I₁ I₂ : Type*} (P : List Graph → Prop) (d : Nat) (h : EnvHistory I₁ I₂) :=
  {k : EnvHistory I₁ I₂ // RecentConnected P d h k}

theorem recentConnected_projects {I₁ I₂ : Type*} (P : List Graph → Prop) (d : Nat)
    {h k : EnvHistory I₁ I₂} (conn : RecentConnected P d h k) : InputConnected P h k := by
  induction conn with
  | refl => exact .refl
  | tail _ step ih =>
    apply ih.tail
    obtain ⟨p,eq,_⟩ := step.2.2
    refine ⟨step.1,step.2.1,?_⟩
    cases p <;> [exact Or.inl eq; exact Or.inr eq]

/-- A shared recent view preserves both older input prefixes, rather than
only the selected process's prefix. -/
theorem recentAdjacent_prefixes {I₁ I₂ : Type*} (d : Nat) {h k : EnvHistory I₁ I₂}
    (adj : RecentAdjacent d h k) (p : Proc) :
    olderInputPrefix p d h = olderInputPrefix p d k := by
  obtain ⟨q,eq,age⟩ := adj
  have adjacent : InputAdjacent h k := by
    cases q <;> [exact Or.inl eq; exact Or.inr eq]
  have len : h.length = k.length := by
    have e := adjacent_same_depth (inputAdjacent_projects adjacent)
    simpa [History.graphSequence] using e
  by_cases same : q = p
  · subst q
    unfold olderInputPrefix
    rw [len, ← ownInputs_current p h, ← ownInputs_current p k, eq]
  · have other : q.other = p := by cases q <;> cases p <;> simp_all [Proc.other]
    have ageK : silentAge (currentView q k) < d := by rwa [← eq]
    have eh := otherInputs_recent_prefix q h d age
    have ek := otherInputs_recent_prefix q k d ageK
    rw [other,len,eq] at eh
    rw [other] at ek
    unfold olderInputPrefix
    rw [len]
    exact eh.symm.trans ek

theorem recentConnected_prefixes {I₁ I₂ : Type*} (P : List Graph → Prop) (d : Nat)
    {h k : EnvHistory I₁ I₂} (conn : RecentConnected P d h k) (p : Proc) :
    olderInputPrefix p d h = olderInputPrefix p d k := by
  induction conn with
  | refl => rfl
  | tail _ step ih => exact ih.trans (recentAdjacent_prefixes d step.2.2 p)

theorem finite_recent_piece {I₁ I₂ : Type*} [Finite I₁] [Finite I₂]
    (P : List Graph → Prop) (bounded : BoundedViewComponents P)
    (d : Nat) (h : EnvHistory I₁ I₂) (live : P (History.graphSequence h)) :
    Finite (RecentPiece P d h) ∧
      Nat.card (RecentPiece P d h) ≤
        Nat.card (HistoryComponent P (History.graphSequence h)) *
          (Nat.card (Fin d → Option (PSum I₁ I₂)))^2 := by
  exact finite_family_of_common_prefixes P bounded d h live (RecentConnected P d h)
    (fun _ conn => recentConnected_projects P d conn)
    (fun _ conn => ⟨recentConnected_prefixes P d conn .one,
      recentConnected_prefixes P d conn .two⟩)

/-- Any old shared view must belong to the selected coordinator. -/
theorem old_view_owner {I₁ I₂ : Type*} (P : List Graph → Prop) (d : Nat)
    (h : EnvHistory I₁ I₂) (p q : Proc)
    (recent : RecentOther P d (History.graphSequence h) p)
    (old : d ≤ silentAge (currentView q h)) : q = p := by
  by_contra different
  have blind : BlindFor d (tagView (graphView q (History.graphSequence h))) := by
    apply silentAge_implies_blindFor
    rw [← eraseView_current, silentAge_erase]
    exact old
  apply recent (History.graphSequence h) _ Relation.ReflTransGen.refl _ _ blind
  · cases q <;> [exact Or.inl rfl; exact Or.inr rfl]
  · cases q <;> exact different

/-- Every original adjacency either stays within a recent piece or shares
an old view of the selected coordinator. This is an exact edge decomposition. -/
theorem adjacent_recent_or_coordinator {I₁ I₂ : Type*} (P : List Graph → Prop) (d : Nat)
    (h k : EnvHistory I₁ I₂) (p : Proc)
    (recent : RecentOther P d (History.graphSequence h) p)
    (adj : InputAdjacent h k) :
    RecentAdjacent d h k ∨
      (currentView p h = currentView p k ∧ d ≤ silentAge (currentView p h)) := by
  have shared : ∃ q, currentView q h = currentView q k := by
    rcases adj with eq | eq
    · exact ⟨.one,eq⟩
    · exact ⟨.two,eq⟩
  obtain ⟨q,eq⟩ := shared
  by_cases young : silentAge (currentView q h) < d
  · exact Or.inl ⟨q,eq,young⟩
  · have age : d ≤ silentAge (currentView q h) := by omega
    have owner := old_view_owner P d h p q recent age
    subst q
    exact Or.inr ⟨eq,age⟩

/-- The bound holds at every live history, not only at coordinator changes. -/
theorem holes_bounded_recent_pieces {I₁ I₂ : Type*} [Finite I₁] [Finite I₂]
    (A : Set (Nat → Graph)) (regular : OmegaRegular A) (holes : GeometricHoles A) :
    ∃ d B, ∀ h : EnvHistory I₁ I₂, LivePrefix A (History.graphSequence h) →
      (Finite (RecentPiece (LivePrefix A) d h) ∧
        Nat.card (RecentPiece (LivePrefix A) d h) ≤ B) ∧
      ∀ k, InputAdjacent h k → RecentAdjacent d h k ∨
        (currentView (componentLeader (LivePrefix A) d (History.graphSequence h)) h =
          currentView (componentLeader (LivePrefix A) d (History.graphSequence h)) k ∧
        d ≤ silentAge (currentView (componentLeader (LivePrefix A) d
          (History.graphSequence h)) h)) := by
  obtain ⟨d,recent⟩ := holes_component_recent_receiver A regular holes
  obtain ⟨K,bound⟩ := (omegaRegular_holes_iff_bounded_components A regular).mp holes
  refine ⟨d,K * (Nat.card (Fin d → Option (PSum I₁ I₂)))^2,?_⟩
  intro h live
  have piece := finite_recent_piece (LivePrefix A) ⟨K,bound⟩ d h live
  refine ⟨⟨piece.1,piece.2.trans (Nat.mul_le_mul_right _ (bound _ live).2)⟩,?_⟩
  intro k adj
  exact adjacent_recent_or_coordinator _ d h k _
    (componentLeader_correct _ _ _ (recent _ live)) adj

end Characterisation
