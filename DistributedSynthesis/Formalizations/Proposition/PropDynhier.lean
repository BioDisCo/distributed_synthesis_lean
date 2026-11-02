/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Definition.DefViews

/-!
# Non-fringe hierarchy

This file formalizes Proposition `prop:dynhier` from `paper.tex`.
-/

namespace DistributedSynthesis

universe u v x y

open NonFringeView

theorem dynhier_left
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hr : r.graph = .left) :
    DirectSubtupleOfReceiver
      (currentNonFringe Proc.two (History.append h r))
      (currentNonFringe Proc.one (History.append h r)) := by
  simp [currentNonFringe, hr, NonFringeView.DirectSubtupleOfReceiver]
  constructor <;> rfl

theorem dynhier_right
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hr : r.graph = .right) :
    DirectSubtupleOfReceiver
      (currentNonFringe Proc.one (History.append h r))
      (currentNonFringe Proc.two (History.append h r)) := by
  simp [currentNonFringe, hr, NonFringeView.DirectSubtupleOfReceiver]
  constructor <;> rfl

theorem dynhier_both
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hr : r.graph = .both) :
    ∃ prevOne prevTwo x₁ x₂,
      currentNonFringe Proc.one (History.append h r) = .quad prevOne x₁ prevTwo x₂ ∧
      currentNonFringe Proc.two (History.append h r) = .quad prevTwo x₂ prevOne x₁ := by
  refine ⟨currentView Proc.one h, currentView Proc.two h, PSum.inl r.inputOne, PSum.inr r.inputTwo, ?_, ?_⟩
  · simp [currentNonFringe, hr, View.nonFringe]
  · simp [currentNonFringe, hr, View.nonFringe]

theorem prop_dynhier
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂) :
    match r.graph with
    | .left =>
        DirectSubtupleOfReceiver
          (currentNonFringe Proc.two (History.append h r))
          (currentNonFringe Proc.one (History.append h r))
    | .right =>
        DirectSubtupleOfReceiver
          (currentNonFringe Proc.one (History.append h r))
          (currentNonFringe Proc.two (History.append h r))
    | .both =>
        ∃ prevOne prevTwo x₁ x₂,
          currentNonFringe Proc.one (History.append h r) = .quad prevOne x₁ prevTwo x₂ ∧
          currentNonFringe Proc.two (History.append h r) = .quad prevTwo x₂ prevOne x₁ := by
  cases hGraph : r.graph with
  | left =>
      exact dynhier_left h r hGraph
  | right =>
      exact dynhier_right h r hGraph
  | both =>
      exact dynhier_both h r hGraph

/--
Paper-facing packaged form of Proposition `prop:dynhier` for a history written
as a prefix followed by its last round.
-/
theorem nonfringe_view_subtuple_structure
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂) :
    (r.graph = .left →
      DirectSubtupleOfReceiver
        (currentNonFringe Proc.two (History.append h r))
        (currentNonFringe Proc.one (History.append h r))) ∧
    (r.graph = .right →
      DirectSubtupleOfReceiver
        (currentNonFringe Proc.one (History.append h r))
        (currentNonFringe Proc.two (History.append h r))) ∧
    (r.graph = .both →
      ∃ prevOne prevTwo x₁ x₂,
        currentNonFringe Proc.one (History.append h r) = .quad prevOne x₁ prevTwo x₂ ∧
        currentNonFringe Proc.two (History.append h r) = .quad prevTwo x₂ prevOne x₁) := by
  constructor
  · intro hleft
    exact dynhier_left h r hleft
  constructor
  · intro hright
    exact dynhier_right h r hright
  · intro hboth
    exact dynhier_both h r hboth

end DistributedSynthesis
