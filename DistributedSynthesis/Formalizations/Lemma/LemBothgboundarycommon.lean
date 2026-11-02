/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemJointviewsdeterminehistory

/-!
# Both boundaries restore common access

This file formalizes Lemma `lem:bothgboundarycommon` from `paper.tex`.
-/

namespace DistributedSynthesis

universe u v w x y

/-- The input/graph data recoverable from a boundary prefix. -/
def boundaryInputGraphData
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂) :
    List Graph × List In₁ × List In₂ :=
  (History.graphSequence h, h.map RoundRecord.inputOne, h.map RoundRecord.inputTwo)

/--
At a final `both` round, process `1`'s current full view explicitly contains
both previous full views and both current inputs.
-/
theorem bothBoundary_procOne_view
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hboth : r.graph = .both) :
    currentView Proc.one (History.append h r) =
      .recv (currentView Proc.one h) (.inl r.inputOne)
        (currentView Proc.two h) (.inr r.inputTwo) := by
  simp [currentView_one_append, hboth]

/--
At a final `both` round, process `2`'s current full view explicitly contains
both previous full views and both current inputs.
-/
theorem bothBoundary_procTwo_view
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hboth : r.graph = .both) :
    currentView Proc.two (History.append h r) =
      .recv (currentView Proc.two h) (.inr r.inputTwo)
        (currentView Proc.one h) (.inl r.inputOne) := by
  simp [currentView_two_append, hboth]

/--
From process `1`'s current view at a final `both` round one can recover the two
previous full views and the current input pair.
-/
theorem bothBoundary_procOne_recovers_data
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hboth : r.graph = .both) :
    ∃ prevOne prevTwo xOne xTwo,
      currentView Proc.one (History.append h r) = .recv prevOne xOne prevTwo xTwo := by
  refine ⟨currentView Proc.one h, currentView Proc.two h, .inl r.inputOne, .inr r.inputTwo, ?_⟩
  exact bothBoundary_procOne_view h r hboth

/--
From process `2`'s current view at a final `both` round one can recover the two
previous full views and the current input pair.
-/
theorem bothBoundary_procTwo_recovers_data
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hboth : r.graph = .both) :
    ∃ prevTwo prevOne xTwo xOne,
      currentView Proc.two (History.append h r) = .recv prevTwo xTwo prevOne xOne := by
  refine ⟨currentView Proc.two h, currentView Proc.one h, .inr r.inputTwo, .inl r.inputOne, ?_⟩
  exact bothBoundary_procTwo_view h r hboth

/--
Process `1`'s current view at a final `both` round determines the previous
view pair and the current input pair.
-/
theorem bothBoundary_procOne_determines_previousViewsAndInputs
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h h' : History In₁ In₂ Graph Out₁ Out₂)
    (r r' : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hboth : r.graph = .both)
    (hboth' : r'.graph = .both)
    (hview :
      currentView Proc.one (History.append h r) =
        currentView Proc.one (History.append h' r')) :
    currentView Proc.one h = currentView Proc.one h' ∧
      currentView Proc.two h = currentView Proc.two h' ∧
      r.inputOne = r'.inputOne ∧ r.inputTwo = r'.inputTwo := by
  rw [bothBoundary_procOne_view h r hboth, bothBoundary_procOne_view h' r' hboth'] at hview
  injection hview with _ hprevOne hinputOne hprevTwo hinputTwo
  exact ⟨hprevOne, hprevTwo, by simpa using hinputOne, by simpa using hinputTwo⟩

/--
Process `2`'s current view at a final `both` round determines the previous
view pair and the current input pair.
-/
theorem bothBoundary_procTwo_determines_previousViewsAndInputs
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h h' : History In₁ In₂ Graph Out₁ Out₂)
    (r r' : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hboth : r.graph = .both)
    (hboth' : r'.graph = .both)
    (hview :
      currentView Proc.two (History.append h r) =
        currentView Proc.two (History.append h' r')) :
    currentView Proc.one h = currentView Proc.one h' ∧
      currentView Proc.two h = currentView Proc.two h' ∧
      r.inputOne = r'.inputOne ∧ r.inputTwo = r'.inputTwo := by
  rw [bothBoundary_procTwo_view h r hboth, bothBoundary_procTwo_view h' r' hboth'] at hview
  injection hview with _ hprevTwo hinputTwo hprevOne hinputOne
  exact ⟨hprevOne, hprevTwo, by simpa using hinputOne, by simpa using hinputTwo⟩

/--
At a final `both` round, process `1`'s current full view determines the whole
input/graph prefix before the boundary and the current input pair.
-/
theorem bothBoundary_procOne_determines_prefix
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h h' : History In₁ In₂ Graph Out₁ Out₂)
    (r r' : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hboth : r.graph = .both)
    (hboth' : r'.graph = .both)
    (hview :
      currentView Proc.one (History.append h r) =
        currentView Proc.one (History.append h' r')) :
    History.graphSequence h = History.graphSequence h' ∧
      History.inputSequence Proc.one h = History.inputSequence Proc.one h' ∧
      History.inputSequence Proc.two h = History.inputSequence Proc.two h' ∧
      r.inputOne = r'.inputOne ∧ r.inputTwo = r'.inputTwo := by
  rw [bothBoundary_procOne_view h r hboth, bothBoundary_procOne_view h' r' hboth'] at hview
  injection hview with _ hprevOne hinputOne hprevTwo hinputTwo
  obtain ⟨hgraphs, hseqOne, hseqTwo⟩ :=
    jointViews_determine_inputSequences h h' hprevOne hprevTwo
  exact ⟨hgraphs, hseqOne, hseqTwo, by simpa using hinputOne, by simpa using hinputTwo⟩

/--
At a final `both` round, process `2`'s current full view determines the whole
input/graph prefix before the boundary and the current input pair.
-/
theorem bothBoundary_procTwo_determines_prefix
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h h' : History In₁ In₂ Graph Out₁ Out₂)
    (r r' : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hboth : r.graph = .both)
    (hboth' : r'.graph = .both)
    (hview :
      currentView Proc.two (History.append h r) =
        currentView Proc.two (History.append h' r')) :
    History.graphSequence h = History.graphSequence h' ∧
      History.inputSequence Proc.one h = History.inputSequence Proc.one h' ∧
      History.inputSequence Proc.two h = History.inputSequence Proc.two h' ∧
      r.inputOne = r'.inputOne ∧ r.inputTwo = r'.inputTwo := by
  rw [bothBoundary_procTwo_view h r hboth, bothBoundary_procTwo_view h' r' hboth'] at hview
  injection hview with _ hprevTwo hinputTwo hprevOne hinputOne
  obtain ⟨hgraphs, hseqOne, hseqTwo⟩ :=
    jointViews_determine_inputSequences h h' hprevOne hprevTwo
  exact ⟨hgraphs, hseqOne, hseqTwo, by simpa using hinputOne, by simpa using hinputTwo⟩

/--
Process `1`'s current view at a final `both` round determines the full
input/graph history through the boundary round.
-/
theorem bothBoundary_procOne_determines_boundaryInputGraphData
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h h' : History In₁ In₂ Graph Out₁ Out₂)
    (r r' : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hboth : r.graph = .both)
    (hboth' : r'.graph = .both)
    (hview :
      currentView Proc.one (History.append h r) =
        currentView Proc.one (History.append h' r')) :
    boundaryInputGraphData (History.append h r) =
      boundaryInputGraphData (History.append h' r') := by
  obtain ⟨hgraphs, hseqOne, hseqTwo, hinputOne, hinputTwo⟩ :=
    bothBoundary_procOne_determines_prefix h h' r r' hboth hboth' hview
  have hmapGraph : h.map RoundRecord.graph = h'.map RoundRecord.graph := by
    simpa [History.graphSequence] using hgraphs
  have hmapOne : h.map RoundRecord.inputOne = h'.map RoundRecord.inputOne := by
    simpa [History.inputSequence] using hseqOne
  have hmapTwo : h.map RoundRecord.inputTwo = h'.map RoundRecord.inputTwo := by
    simpa [History.inputSequence] using hseqTwo
  simp [boundaryInputGraphData, History.graphSequence, History.append, hboth, hboth',
    hmapGraph, hmapOne, hmapTwo, hinputOne, hinputTwo]

/--
Process `2`'s current view at a final `both` round determines the full
input/graph history through the boundary round.
-/
theorem bothBoundary_procTwo_determines_boundaryInputGraphData
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h h' : History In₁ In₂ Graph Out₁ Out₂)
    (r r' : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hboth : r.graph = .both)
    (hboth' : r'.graph = .both)
    (hview :
      currentView Proc.two (History.append h r) =
        currentView Proc.two (History.append h' r')) :
    boundaryInputGraphData (History.append h r) =
      boundaryInputGraphData (History.append h' r') := by
  obtain ⟨hgraphs, hseqOne, hseqTwo, hinputOne, hinputTwo⟩ :=
    bothBoundary_procTwo_determines_prefix h h' r r' hboth hboth' hview
  have hmapGraph : h.map RoundRecord.graph = h'.map RoundRecord.graph := by
    simpa [History.graphSequence] using hgraphs
  have hmapOne : h.map RoundRecord.inputOne = h'.map RoundRecord.inputOne := by
    simpa [History.inputSequence] using hseqOne
  have hmapTwo : h.map RoundRecord.inputTwo = h'.map RoundRecord.inputTwo := by
    simpa [History.inputSequence] using hseqTwo
  simp [boundaryInputGraphData, History.graphSequence, History.append, hboth, hboth',
    hmapGraph, hmapOne, hmapTwo, hinputOne, hinputTwo]

/--
Consequently, any boundary observation component computed from the recovered
input/graph boundary prefix is consistently determined by process `1`'s view.
-/
theorem bothBoundary_procOne_boundaryComponent_eq
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    {Component : Type w}
    (component : List Graph × List In₁ × List In₂ -> Component)
    (h h' : History In₁ In₂ Graph Out₁ Out₂)
    (r r' : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hboth : r.graph = .both)
    (hboth' : r'.graph = .both)
    (hview :
      currentView Proc.one (History.append h r) =
        currentView Proc.one (History.append h' r')) :
    component (boundaryInputGraphData (History.append h r)) =
      component (boundaryInputGraphData (History.append h' r')) := by
  rw [bothBoundary_procOne_determines_boundaryInputGraphData h h' r r' hboth hboth' hview]

/--
Consequently, any boundary observation component computed from the recovered
input/graph boundary prefix is consistently determined by process `2`'s view.
-/
theorem bothBoundary_procTwo_boundaryComponent_eq
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    {Component : Type w}
    (component : List Graph × List In₁ × List In₂ -> Component)
    (h h' : History In₁ In₂ Graph Out₁ Out₂)
    (r r' : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hboth : r.graph = .both)
    (hboth' : r'.graph = .both)
    (hview :
      currentView Proc.two (History.append h r) =
        currentView Proc.two (History.append h' r')) :
    component (boundaryInputGraphData (History.append h r)) =
      component (boundaryInputGraphData (History.append h' r')) := by
  rw [bothBoundary_procTwo_determines_boundaryInputGraphData h h' r r' hboth hboth' hview]

/--
Lemma `lem:bothgboundarycommon`: at a final `both` boundary, either
process's current full view determines every finite boundary component
computed from the recovered input/graph boundary prefix.
-/
theorem both_boundaries_restore_common_access
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
  cases p
  · exact bothBoundary_procOne_boundaryComponent_eq component h h' r r' hboth hboth' hview
  · exact bothBoundary_procTwo_boundaryComponent_eq component h h' r r' hboth hboth' hview

end DistributedSynthesis
