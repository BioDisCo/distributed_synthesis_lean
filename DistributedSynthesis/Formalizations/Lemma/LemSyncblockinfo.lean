/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Lemma.LemBothgboundarycommon
import DistributedSynthesis.Formalizations.Proposition.PropDynhier

/-!
# Information structure inside synchronized one-directional blocks

This file packages Lemma `lem:syncblockinfo` from `paper.tex`.
-/

namespace DistributedSynthesis

universe u v w x y

/-- In a left block, process `2` is the sender and its current view records no receive. -/
theorem syncBlock_left_sender_view
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hr : r.graph = .left) :
    currentView Proc.two (History.append h r) =
      .noRecv (currentView Proc.two h) (.inr r.inputTwo) := by
  simp [currentView_two_append, hr]

/-- In a right block, process `1` is the sender and its current view records no receive. -/
theorem syncBlock_right_sender_view
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hr : r.graph = .right) :
    currentView Proc.one (History.append h r) =
      .noRecv (currentView Proc.one h) (.inl r.inputOne) := by
  simp [currentView_one_append, hr]

/-- For process `2`, a no-receive tag after one appended round identifies graph `left`. -/
theorem procTwo_noRecv_iff_left
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂) :
    (currentView Proc.two (History.append h r)).receiptTag = .noRecv ↔
      r.graph = .left := by
  cases hgraph : r.graph <;> simp [currentView_two_append, hgraph, View.receiptTag]

/-- For process `1`, a no-receive tag after one appended round identifies graph `right`. -/
theorem procOne_noRecv_iff_right
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂) :
    (currentView Proc.one (History.append h r)).receiptTag = .noRecv ↔
      r.graph = .right := by
  cases hgraph : r.graph <;> simp [currentView_one_append, hgraph, View.receiptTag]

/-- In a left block, process `1` receives the sender's previous view and current input. -/
theorem syncBlock_left_receiver_view
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hr : r.graph = .left) :
    currentView Proc.one (History.append h r) =
      .recv (currentView Proc.one h) (.inl r.inputOne)
        (currentView Proc.two h) (.inr r.inputTwo) := by
  simp [currentView_one_append, hr]

/-- In a right block, process `2` receives the sender's previous view and current input. -/
theorem syncBlock_right_receiver_view
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hr : r.graph = .right) :
    currentView Proc.two (History.append h r) =
      .recv (currentView Proc.two h) (.inr r.inputTwo)
        (currentView Proc.one h) (.inl r.inputOne) := by
  simp [currentView_two_append, hr]

/--
At a starting `both` boundary, any boundary component computed from the
input/graph prefix is common to both processes.
-/
theorem syncBlock_boundary_common_component
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    {Component : Type w}
    (p : Proc)
    (component : List Graph × List In₁ × List In₂ -> Component)
    (h h' : History In₁ In₂ Graph Out₁ Out₂)
    (r r' : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hboth : r.graph = .both)
    (hboth' : r'.graph = .both)
    (hview :
      currentView p (History.append h r) =
        currentView p (History.append h' r')) :
    component (boundaryInputGraphData (History.append h r)) =
      component (boundaryInputGraphData (History.append h' r')) := by
  exact both_boundaries_restore_common_access p component h h' r r' hboth hboth' hview

/--
Paper-facing Lemma `lem:syncblockinfo`: the two synchronized block
orientations have the stated sender/receiver view equations, sender
no-receive graph identification, and common boundary access.
-/
theorem information_structure_within_synchronized_block
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y} :
    (∀ (h : History In₁ In₂ Graph Out₁ Out₂)
        (r : RoundRecord In₁ In₂ Graph Out₁ Out₂),
      r.graph = .left ->
        currentView Proc.two (History.append h r) =
          .noRecv (currentView Proc.two h) (.inr r.inputTwo)) ∧
    (∀ (h : History In₁ In₂ Graph Out₁ Out₂)
        (r : RoundRecord In₁ In₂ Graph Out₁ Out₂),
      (currentView Proc.two (History.append h r)).receiptTag = .noRecv ↔
        r.graph = .left) ∧
    (∀ (h : History In₁ In₂ Graph Out₁ Out₂)
        (r : RoundRecord In₁ In₂ Graph Out₁ Out₂),
      r.graph = .left ->
        currentView Proc.one (History.append h r) =
          .recv (currentView Proc.one h) (.inl r.inputOne)
            (currentView Proc.two h) (.inr r.inputTwo)) ∧
    (∀ (h : History In₁ In₂ Graph Out₁ Out₂)
        (r : RoundRecord In₁ In₂ Graph Out₁ Out₂),
      r.graph = .right ->
        currentView Proc.one (History.append h r) =
          .noRecv (currentView Proc.one h) (.inl r.inputOne)) ∧
    (∀ (h : History In₁ In₂ Graph Out₁ Out₂)
        (r : RoundRecord In₁ In₂ Graph Out₁ Out₂),
      (currentView Proc.one (History.append h r)).receiptTag = .noRecv ↔
        r.graph = .right) ∧
    (∀ (h : History In₁ In₂ Graph Out₁ Out₂)
        (r : RoundRecord In₁ In₂ Graph Out₁ Out₂),
      r.graph = .right ->
        currentView Proc.two (History.append h r) =
          .recv (currentView Proc.two h) (.inr r.inputTwo)
            (currentView Proc.one h) (.inl r.inputOne)) := by
  exact ⟨
    syncBlock_left_sender_view,
    procTwo_noRecv_iff_left,
    syncBlock_left_receiver_view,
    syncBlock_right_sender_view,
    procOne_noRecv_iff_right,
    syncBlock_right_receiver_view⟩

end DistributedSynthesis
