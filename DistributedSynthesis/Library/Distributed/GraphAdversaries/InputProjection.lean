/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.GraphAdversaries.ComponentBounds

/-! Forgetting private inputs projects actual local indistinguishability into
the graph-only model. Fibres of this projection need not be bounded. -/
namespace Characterisation
open DistributedSynthesis FullViewPath

private def eraseInput {I₁ I₂ : Type*} : PSum I₁ I₂ → PSum Unit Unit
  | .inl _ => .inl ()
  | .inr _ => .inr ()

def eraseView {I₁ I₂ : Type*} : {p : Proc} → View I₁ I₂ p → View Unit Unit p
  | _, .empty p => .empty p
  | _, .noRecv v i => .noRecv (eraseView v) (eraseInput i)
  | _, .recv v i w j => .recv (eraseView v) (eraseInput i) (eraseView w) (eraseInput j)

/-- Erasing the input values of an actual view gives the graph-only view. -/
theorem eraseView_history {I₁ I₂ O₁ O₂ : Type*} (h : History I₁ I₂ Graph O₁ O₂) :
    eraseView (currentView .one h) = (evaluate (History.graphSequence h)).one ∧
    eraseView (currentView .two h) = (evaluate (History.graphSequence h)).two := by
  induction h using List.reverseRecOn with
  | nil => exact ⟨rfl, rfl⟩
  | append_singleton h r ih =>
    erw [History.graphSequence_append, at_append]
    change eraseView (currentView .one (History.append h r)) = _ ∧
      eraseView (currentView .two (History.append h r)) = _
    rw [currentView_one_append, currentView_two_append]
    cases hg : r.graph <;>
      simp [advance, advanceViews, eraseView, eraseInput, Proc.other, ih]

def InputAdjacent {I₁ I₂ O₁ O₂ : Type*} (h k : History I₁ I₂ Graph O₁ O₂) : Prop :=
  currentView .one h = currentView .one k ∨ currentView .two h = currentView .two k

theorem inputAdjacent_projects {I₁ I₂ O₁ O₂ : Type*}
    {h k : History I₁ I₂ Graph O₁ O₂} (adj : InputAdjacent h k) :
    Adjacent (History.graphSequence h) (History.graphSequence k) := by
  rcases adj with eq | eq
  · exact Or.inl ((eraseView_history h).1.symm.trans
      ((congrArg eraseView eq).trans (eraseView_history k).1))
  · exact Or.inr ((eraseView_history h).2.symm.trans
      ((congrArg eraseView eq).trans (eraseView_history k).2))

def InputConnected {I₁ I₂ O₁ O₂ : Type*} (P : List Graph → Prop) :
    History I₁ I₂ Graph O₁ O₂ → History I₁ I₂ Graph O₁ O₂ → Prop :=
  Relation.ReflTransGen (fun h k => P (History.graphSequence h) ∧
    P (History.graphSequence k) ∧ InputAdjacent h k)

theorem inputConnected_projects {I₁ I₂ O₁ O₂ : Type*} (P : List Graph → Prop)
    {h k : History I₁ I₂ Graph O₁ O₂} (conn : InputConnected P h k) :
    Connected P (History.graphSequence h) (History.graphSequence k) := by
  apply Relation.ReflTransGen.lift History.graphSequence _ conn
  intro u v step
  exact ⟨step.1, step.2.1, inputAdjacent_projects step.2.2⟩

/-- Distinct graph histories represented inside an input-dependent component. -/
def ComponentGraphHistories {I₁ I₂ O₁ O₂ : Type*} (P : List Graph → Prop)
    (h : History I₁ I₂ Graph O₁ O₂) :=
  {g : List Graph // ∃ k, InputConnected P h k ∧ History.graphSequence k = g}

/-- Graph holes bound the number of graph histories represented in each
input-dependent component, even when its input histories are unbounded. -/
theorem bounded_component_graph_histories {I₁ I₂ O₁ O₂ : Type*}
    (P : List Graph → Prop) (bounded : BoundedViewComponents P) :
    ∃ K, ∀ h : History I₁ I₂ Graph O₁ O₂, P (History.graphSequence h) →
      Finite (ComponentGraphHistories P h) ∧ Nat.card (ComponentGraphHistories P h) ≤ K := by
  obtain ⟨K, bound⟩ := bounded
  refine ⟨K, ?_⟩
  intro h hh
  let f : ComponentGraphHistories P h → HistoryComponent P (History.graphSequence h) :=
    fun g => ⟨g.val, by
      obtain ⟨k, hc, he⟩ := g.property
      rw [← he]
      exact inputConnected_projects P hc⟩
  have inj : Function.Injective f := by
    intro g j eq
    apply Subtype.ext
    exact congrArg (fun z : HistoryComponent P (History.graphSequence h) => z.val) eq
  letI : Finite (HistoryComponent P (History.graphSequence h)) := (bound _ hh).1
  have finite := Finite.of_injective f inj
  exact ⟨finite, (Nat.card_le_card_of_injective f inj).trans (bound _ hh).2⟩

theorem holes_bound_input_component_graph_histories {I₁ I₂ O₁ O₂ : Type*}
    (A : Set (Nat → Graph)) (regular : OmegaRegular A) (holes : GeometricHoles A) :
    ∃ K, ∀ h : History I₁ I₂ Graph O₁ O₂, LivePrefix A (History.graphSequence h) →
      Finite (ComponentGraphHistories (LivePrefix A) h) ∧
      Nat.card (ComponentGraphHistories (LivePrefix A) h) ≤ K :=
  bounded_component_graph_histories _ ((omegaRegular_holes_iff_bounded_components A regular).mp holes)

end Characterisation
