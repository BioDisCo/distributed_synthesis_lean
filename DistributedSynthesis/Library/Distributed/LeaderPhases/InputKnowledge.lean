/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.ComponentLeader

/-! Input information carried by full views, including inputs in delivered
messages. These projections do not inspect the actual graph history. -/
namespace Characterisation
open DistributedSynthesis FullViewPath

/-- The complete own-input word retained in a local view. -/
def ownInputs {I₁ I₂ : Type*} : {p : Proc} → View I₁ I₂ p → List (PSum I₁ I₂)
  | _, .empty _ => []
  | _, .noRecv v i => ownInputs v ++ [i]
  | _, .recv v i _ _ => ownInputs v ++ [i]

/-- The other process's input prefix disclosed by the most recent reception. -/
def otherInputs {I₁ I₂ : Type*} : {p : Proc} → View I₁ I₂ p → List (PSum I₁ I₂)
  | _, .empty _ => []
  | _, .noRecv v _ => otherInputs v
  | _, .recv _ _ w j => ownInputs w ++ [j]

def silentAge {I₁ I₂ : Type*} : {p : Proc} → View I₁ I₂ p → Nat
  | _, .empty _ => 0
  | _, .noRecv v _ => silentAge v + 1
  | _, .recv _ _ _ _ => 0

def inputWord {I₁ I₂ O₁ O₂ : Type*} (p : Proc) (h : History I₁ I₂ Graph O₁ O₂) :
    List (PSum I₁ I₂) := h.map (RoundRecord.input p)

theorem ownInputs_history {I₁ I₂ O₁ O₂ : Type*} (h : History I₁ I₂ Graph O₁ O₂) :
    ownInputs (currentView .one h) = inputWord .one h ∧
    ownInputs (currentView .two h) = inputWord .two h := by
  induction h using List.reverseRecOn with
  | nil => exact ⟨rfl,rfl⟩
  | append_singleton h r ih =>
    change ownInputs (currentView .one (History.append h r)) = _ ∧
      ownInputs (currentView .two (History.append h r)) = _
    rw [currentView_one_append, currentView_two_append]
    cases hg : r.graph <;> simp [ownInputs, inputWord, ih]

theorem silentAge_erase {I₁ I₂ : Type*} {p : Proc} (v : View I₁ I₂ p) :
    silentAge (eraseView v) = silentAge v := by
  induction v with
  | empty => rfl
  | noRecv v i ih => simp [eraseView, silentAge, ih]
  | recv => rfl

/-- The known prefix ends precisely before the consecutive nonreceiving suffix. -/
theorem otherInputs_history {I₁ I₂ O₁ O₂ : Type*} (h : History I₁ I₂ Graph O₁ O₂) :
    (otherInputs (currentView .one h) =
      (inputWord .two h).take (h.length - silentAge (currentView .one h)) ∧
      silentAge (currentView .one h) ≤ h.length) ∧
    (otherInputs (currentView .two h) =
      (inputWord .one h).take (h.length - silentAge (currentView .two h)) ∧
      silentAge (currentView .two h) ≤ h.length) := by
  induction h using List.reverseRecOn with
  | nil => exact ⟨⟨rfl,le_rfl⟩,⟨rfl,le_rfl⟩⟩
  | append_singleton h r ih =>
    have own := ownInputs_history h
    change (_ = _ ∧ _) ∧ (_ = _ ∧ _)
    have one := currentView_one_append h r
    have two := currentView_two_append h r
    change currentView .one (h ++ [r]) = _ at one
    change currentView .two (h ++ [r]) = _ at two
    rw [one, two]
    cases hg : r.graph <;>
      simp [otherInputs, silentAge, Proc.other, History.length, own, inputWord,
        List.take_append, ih.1.1, ih.2.1]
    all_goals first | exact ih.1.2 | exact ih.2.2

def tagView : {p : Proc} → View Unit Unit p → Vertex
  | .one, v => .inl v
  | .two, v => .inr v

def graphView (p : Proc) (h : List Graph) : View Unit Unit p :=
  match p with
  | .one => (evaluate h).one
  | .two => (evaluate h).two

/-- A sufficiently long nonreceiving suffix is the geometric blind suffix. -/
theorem silentAge_implies_blindFor (d : Nat) (p : Proc) (h : List Graph)
    (hd : d ≤ silentAge (graphView p h)) : BlindFor d (tagView (graphView p h)) := by
  induction d generalizing p h with
  | zero => exact ⟨_, rfl⟩
  | succ d ih =>
    cases h using List.reverseRecOn with
    | nil => cases p <;> simp [graphView, evaluate, root, silentAge] at hd
    | append_singleton h g =>
      cases p <;> cases g <;>
        simp only [graphView, at_append, advance, advanceViews, silentAge] at hd ⊢
      all_goals first
        | omega
        | obtain ⟨v,hv⟩ := ih .one h (by exact Nat.le_of_succ_le_succ hd)
          refine ⟨v, ?_⟩
          rw [Function.iterate_succ_apply', hv]
          rfl
        | obtain ⟨v,hv⟩ := ih .two h (by exact Nat.le_of_succ_le_succ hd)
          refine ⟨v, ?_⟩
          rw [Function.iterate_succ_apply', hv]
          rfl

theorem ownInputs_current {I₁ I₂ O₁ O₂ : Type*} (p : Proc)
    (h : History I₁ I₂ Graph O₁ O₂) : ownInputs (currentView p h) = inputWord p h := by
  cases p
  · exact (ownInputs_history h).1
  · exact (ownInputs_history h).2

theorem eraseView_current {I₁ I₂ O₁ O₂ : Type*} (p : Proc)
    (h : History I₁ I₂ Graph O₁ O₂) :
    eraseView (currentView p h) = graphView p (History.graphSequence h) := by
  cases p
  · exact (eraseView_history h).1
  · exact (eraseView_history h).2

theorem otherInputs_recent_prefix {I₁ I₂ O₁ O₂ : Type*} (p : Proc)
    (h : History I₁ I₂ Graph O₁ O₂) (d : Nat)
    (recent : silentAge (currentView p h) < d) :
    (otherInputs (currentView p h)).take (h.length-d) =
      (inputWord p.other h).take (h.length-d) := by
  have eq : otherInputs (currentView p h) =
      (inputWord p.other h).take (h.length - silentAge (currentView p h)) := by
    cases p
    · exact (otherInputs_history h).1.1
    · exact (otherInputs_history h).2.1
  rw [eq, List.take_take, min_eq_left (by omega)]

def olderInputPrefix {I₁ I₂ O₁ O₂ : Type*} (p : Proc) (d : Nat)
    (h : History I₁ I₂ Graph O₁ O₂) := (inputWord p h).take (h.length-d)

/-- A shared local view preserves the selected process's older input prefix:
either it is the owner's own view, or it has recently received from the owner. -/
theorem selected_prefix_shared_view {I₁ I₂ O₁ O₂ : Type*}
    (P : List Graph → Prop) (d : Nat) (p q : Proc)
    (h k : History I₁ I₂ Graph O₁ O₂)
    (recent : RecentOther P d (History.graphSequence h) p)
    (sameView : currentView q h = currentView q k) :
    olderInputPrefix p d h = olderInputPrefix p d k := by
  have adj : InputAdjacent h k := by cases q <;> [exact Or.inl sameView; exact Or.inr sameView]
  have len : h.length = k.length := by
    have eq := adjacent_same_depth (inputAdjacent_projects adj)
    simpa [History.graphSequence] using eq
  unfold olderInputPrefix
  rw [len]
  by_cases qp : q = p
  · subst q
    rw [← ownInputs_current p h, ← ownInputs_current p k, sameView]
  · have other : q.other = p := by cases q <;> cases p <;> simp_all [Proc.other]
    have noBlind : ¬ BlindFor d (tagView (graphView q (History.graphSequence h))) := by
      apply recent (History.graphSequence h) _ Relation.ReflTransGen.refl
      · cases q <;> [exact Or.inl rfl; exact Or.inr rfl]
      · cases q <;> exact qp
    have ageH : silentAge (currentView q h) < d := by
      by_contra bad
      apply noBlind
      apply silentAge_implies_blindFor
      rw [← eraseView_current, silentAge_erase]
      omega
    have ageK : silentAge (currentView q k) < d := by rwa [← sameView]
    have eh := otherInputs_recent_prefix q h d ageH
    have ek := otherInputs_recent_prefix q k d ageK
    rw [other, len, sameView] at eh
    rw [other] at ek
    exact eh.symm.trans ek

/-- The selected input prefix is constant on the entire input-dependent
component, not just on a process's immediate indistinguishability class. -/
theorem selected_prefix_component {I₁ I₂ O₁ O₂ : Type*}
    (P : List Graph → Prop) (d : Nat) (p : Proc)
    {h k : History I₁ I₂ Graph O₁ O₂}
    (recent : RecentOther P d (History.graphSequence h) p)
    (conn : InputConnected P h k) : olderInputPrefix p d h = olderInputPrefix p d k := by
  induction conn with
  | refl => rfl
  | @tail a b conn step ih =>
    have recentA := (recentOther_component_invariant P d (inputConnected_projects P conn) p).mp recent
    apply ih.trans
    rcases step.2.2 with same | same
    · exact selected_prefix_shared_view P d p .one a b recentA same
    · exact selected_prefix_shared_view P d p .two a b recentA same

theorem holes_common_older_input_prefix {I₁ I₂ O₁ O₂ : Type*}
    (A : Set (Nat → Graph)) (regular : OmegaRegular A) (holes : GeometricHoles A) :
    ∃ d, ∀ h : History I₁ I₂ Graph O₁ O₂, LivePrefix A (History.graphSequence h) →
      ∃ p, ∀ k, InputConnected (LivePrefix A) h k →
        olderInputPrefix p d h = olderInputPrefix p d k := by
  obtain ⟨d, recent⟩ := holes_component_recent_receiver A regular holes
  refine ⟨d, ?_⟩
  intro h hh
  obtain ⟨p,hp⟩ := recent (History.graphSequence h) hh
  exact ⟨p, fun k conn => selected_prefix_component _ d p hp conn⟩

end Characterisation
